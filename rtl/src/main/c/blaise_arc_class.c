/*
 * Blaise RTL — class ARC (function-pointer-dependent subset)
 *
 * _ClassAlloc and _ClassRelease remain in C because they store and call a
 * function pointer (the field-cleanup hook emitted by the compiler as
 * $_FieldCleanup_TypeName).  All other ARC functions live in blaise_arc.pas.
 *
 * Class instance layout:
 *   +--[4 bytes]--+--[4 bytes]--+--[8 bytes]--+--[user fields...]--+
 *   | RefCount    | (padding)   | cleanup ptr | ...                |
 *   +-------------+-------------+-------------+--------------------+
 *                                              ^--- user pointer
 */

#include <stdint.h>
#include <stdlib.h>

typedef void (*BlaiseFieldCleanupFn)(void*);

typedef struct {
    int32_t              refcnt;
    int32_t              _pad;
    BlaiseFieldCleanupFn cleanup;
} BlaiseObjHdr;

#define CLASS_HDR_SIZE (sizeof(BlaiseObjHdr))

static inline BlaiseObjHdr* obj_hdr(void* user_ptr) {
    return (BlaiseObjHdr*)((char*)user_ptr - CLASS_HDR_SIZE);
}

void* _ClassAlloc(size_t size, BlaiseFieldCleanupFn cleanup) {
    char* base = (char*)calloc(1, size + CLASS_HDR_SIZE);
    if (!base) return NULL;
    BlaiseObjHdr* h = (BlaiseObjHdr*)base;
    h->cleanup = cleanup;
    return base + CLASS_HDR_SIZE;
}

/* Forward declaration — implemented in blaise_weak.c. */
extern void _WeakZeroSlots(void* target);

void _ClassRelease(void* user_ptr) {
    if (!user_ptr) return;
    BlaiseObjHdr* h = obj_hdr(user_ptr);
    if (--h->refcnt == 0) {
        _WeakZeroSlots(user_ptr);
        if (h->cleanup) h->cleanup(user_ptr);
        free((char*)user_ptr - CLASS_HDR_SIZE);
    }
}
