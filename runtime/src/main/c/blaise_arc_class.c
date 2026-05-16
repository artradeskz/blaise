/*
 * Blaise — An Object Pascal Compiler
 * Copyright (c) 2026 Graeme Geldenhuys
 * SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
 * Licensed under the Apache License v2.0 with Runtime Library Exception.
 * See LICENSE file in the project root for full license terms.
 *
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
#include <stdio.h>

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

/* Diagnostic helper called from _StringRelease before freeing a string.
   Verifies the header looks sane.  On failure, prints a clear message
   to stderr and aborts so the bug is obvious instead of a wild segfault
   inside libc or blaise_mem.  Compiled-in but cheap when called only on
   the free path. */
void _StringReleaseCheck(void* data_ptr, int32_t refcnt,
                         int32_t length, int32_t capacity) {
    /* refcnt sanity: must be non-negative when reached here (caller
       already filtered IMMORTAL = -1).  Negative = double-free. */
    if (refcnt < -1) {
        fprintf(stderr,
            "blaise: _StringRelease saw a string with refcount = %d "
            "(double-free?) at data_ptr=%p\n", refcnt, data_ptr);
        abort();
    }
    /* length sanity: 0 .. 1 GiB.  Anything beyond is almost certainly
       a corrupted header (ASCII bytes in the length slot, etc). */
    if (length < 0 || length > (1 << 30)) {
        fprintf(stderr,
            "blaise: _StringRelease saw length=%d at data_ptr=%p "
            "(corrupted header)\n", length, data_ptr);
        abort();
    }
    /* capacity must be at least length and not crazy. */
    if (capacity < length || capacity > (1 << 30)) {
        fprintf(stderr,
            "blaise: _StringRelease saw capacity=%d (length=%d) at "
            "data_ptr=%p (corrupted header)\n",
            capacity, length, data_ptr);
        abort();
    }
}

/* Abstract-method tombstone.
 *
 * The compiler emits references to this symbol in two places:
 *   1. Vtable slots for `virtual; abstract` methods on an abstract class.
 *      In normal use these are overwritten by the subclass's vtable when
 *      the abstract class cannot itself be instantiated, but the abstract
 *      class's own vtable still references this stub so that the IR links.
 *   2. Interface dispatch tables (itabs) that map a class's interfaces to
 *      methods which happen to be abstract on that class.
 *
 * The function should be statically unreachable in correct programs.  If
 * control somehow reaches it (e.g. a future direct vtable dispatch on an
 * abstract class), abort with a clear message so the bug is obvious. */
void _AbstractMethodError(void) {
    fprintf(stderr,
        "Runtime error: abstract method called.\n"
        "This indicates a bug in the compiler or RTL — a vtable slot that\n"
        "should have been overridden was dispatched instead.\n");
    abort();
}
