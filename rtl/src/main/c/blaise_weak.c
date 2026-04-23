/*
 * Blaise RTL — Zeroing weak references.
 *
 * A weak reference is a slot (variable or field) pointing at a class
 * instance without contributing to its refcount.  When the backing
 * object's last strong reference is released and the object is about to
 * be freed, every registered weak slot pointing at it is nil'd — so a
 * subsequent dereference sees 0 rather than dangling memory.
 *
 * Design: one global open-chained hash table, keyed on the user_ptr of
 * the backing object.  Each entry carries a linked list of slot
 * addresses (pointers-to-pointers) that reference it.  Inserts and
 * removals are O(bucket-chain + slot-list) — acceptable because weak
 * references are rare relative to strong references.
 *
 * Single-threaded today: Blaise programs run on a single OS thread, so
 * no locking is needed.  When threading arrives, a global mutex around
 * the table (or a finer-grained strategy) will be required.
 *
 * API:
 *   _WeakAssign(slot, new_target) — register slot under new_target and
 *                                   store new_target at *slot; any prior
 *                                   registration for *slot is removed.
 *                                   new_target may be NULL (just unregister).
 *   _WeakClear(slot)              — unregister and zero *slot.  Called at
 *                                   scope exit and field cleanup for weak
 *                                   declarations.
 *   _WeakZeroSlots(target)        — nil every slot pointing at target and
 *                                   drop target's entry from the table.
 *                                   Called from _ClassRelease at refcount
 *                                   zero, before the field-cleanup fn
 *                                   runs and before the block is freed.
 */

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

#define WEAK_BUCKETS 256  /* power of two for a cheap mask on the hash */

typedef struct WeakSlot {
    void**           addr;
    struct WeakSlot* next;
} WeakSlot;

typedef struct WeakEntry {
    void*              target;
    WeakSlot*          slots;
    struct WeakEntry*  next;
} WeakEntry;

static WeakEntry* weak_table[WEAK_BUCKETS];

static unsigned weak_hash(void* ptr) {
    /* Pointers are typically 16-byte-aligned by our allocator, so the low
     * 4 bits are zero — shift them out before masking so nearby
     * allocations don't collide on the same bucket. */
    return (unsigned)(((uintptr_t)ptr >> 4) & (WEAK_BUCKETS - 1));
}

static WeakEntry* weak_find_or_create(void* target) {
    unsigned h = weak_hash(target);
    WeakEntry* e = weak_table[h];
    while (e) {
        if (e->target == target) return e;
        e = e->next;
    }
    e = (WeakEntry*)malloc(sizeof(WeakEntry));
    if (!e) return NULL;
    e->target = target;
    e->slots  = NULL;
    e->next   = weak_table[h];
    weak_table[h] = e;
    return e;
}

/* Remove `slot` from whatever entry currently registers it.  Walks the
 * bucket chain for the slot's current *slot value; the common case is
 * a previous _WeakAssign to this slot, so we have exactly one place to
 * look.  If *slot is NULL there's nothing registered — fast path. */
static void weak_unregister(void** slot) {
    void* target = *slot;
    if (!target) return;
    unsigned h = weak_hash(target);
    WeakEntry* e = weak_table[h];
    while (e) {
        if (e->target == target) {
            WeakSlot** pp = &e->slots;
            while (*pp) {
                if ((*pp)->addr == slot) {
                    WeakSlot* dead = *pp;
                    *pp = dead->next;
                    free(dead);
                    return;
                }
                pp = &(*pp)->next;
            }
            return;
        }
        e = e->next;
    }
}

void _WeakAssign(void** slot, void* new_target) {
    if (!slot) return;
    weak_unregister(slot);
    *slot = new_target;
    if (new_target) {
        WeakEntry* e = weak_find_or_create(new_target);
        if (!e) return;  /* OOM — slot is still assigned, just unlinked */
        WeakSlot* s = (WeakSlot*)malloc(sizeof(WeakSlot));
        if (!s) return;
        s->addr = slot;
        s->next = e->slots;
        e->slots = s;
    }
}

void _WeakClear(void** slot) {
    if (!slot) return;
    weak_unregister(slot);
    *slot = NULL;
}

/* Called by _ClassRelease at refcount zero, before the field-cleanup fn
 * and before free().  Zero every slot registered against target and
 * drop the entry. */
void _WeakZeroSlots(void* target) {
    if (!target) return;
    unsigned h = weak_hash(target);
    WeakEntry** pp = &weak_table[h];
    while (*pp) {
        if ((*pp)->target == target) {
            WeakEntry* dead = *pp;
            WeakSlot*  s    = dead->slots;
            while (s) {
                WeakSlot* ns = s->next;
                *s->addr = NULL;   /* nil the weak slot in caller space */
                free(s);
                s = ns;
            }
            *pp = dead->next;
            free(dead);
            return;
        }
        pp = &(*pp)->next;
    }
}
