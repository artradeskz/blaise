/*
 * Blaise RTL — ARC string management (Phase 2)
 *
 * String pointer convention:
 *   A Blaise string value is a pointer to the 12-byte header below.
 *   The character data starts immediately after the header.
 *   nil (0) represents an empty / unassigned string.
 *
 *   +--[4 bytes]--+--[4 bytes]--+--[4 bytes]--+--[N bytes]--+--[1 byte]--+
 *   | RefCount    | Length      | Capacity    | UTF-8 data  | NUL        |
 *   +-------------+-------------+-------------+-------------+------------+
 *   ^--- string pointer (header ptr)              ^--- chars at ptr+12
 *
 * RefCount = -1 marks a statically-allocated string (string literals in the
 * data section). _StringAddRef and _StringRelease are no-ops for static
 * strings and nil pointers.
 *
 * _StringConcat allocates a new header with RefCount = 0 (unowned). The
 * compiler inserts a _StringAddRef at every assignment, which brings the
 * count to 1. A corresponding _StringRelease at scope exit frees it.
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define IMMORTAL_REFCNT (-1)

typedef struct {
    int32_t refcnt;
    int32_t length;
    int32_t capacity;
    /* char data[]; follows immediately */
} BlaiseStrHdr;

static inline BlaiseStrHdr* hdr(void* ptr) {
    return (BlaiseStrHdr*)ptr;
}

void _StringAddRef(void* ptr) {
    if (!ptr) return;
    BlaiseStrHdr* h = hdr(ptr);
    if (h->refcnt == IMMORTAL_REFCNT) return;
    h->refcnt++;
}

void _StringRelease(void* ptr) {
    if (!ptr) return;
    BlaiseStrHdr* h = hdr(ptr);
    if (h->refcnt == IMMORTAL_REFCNT) return;
    if (--h->refcnt == 0) free(ptr);
}

/*
 * Concatenate two Blaise strings.  Either or both may be nil.
 * Returns a new header with RefCount = 0 (caller takes ownership via AddRef).
 * Returns nil if both inputs are nil.
 */
void* _StringConcat(void* s1, void* s2) {
    const char* c1     = s1 ? (const char*)s1 + sizeof(BlaiseStrHdr) : "";
    const char* c2     = s2 ? (const char*)s2 + sizeof(BlaiseStrHdr) : "";
    int32_t     len1   = s1 ? hdr(s1)->length : 0;
    int32_t     len2   = s2 ? hdr(s2)->length : 0;
    int32_t     total  = len1 + len2;
    BlaiseStrHdr* result;

    result = (BlaiseStrHdr*)malloc(sizeof(BlaiseStrHdr) + total + 1);
    if (!result) return NULL;

    result->refcnt   = 0;   /* unowned; caller's _StringAddRef brings it to 1 */
    result->length   = total;
    result->capacity = total;

    char* dest = (char*)result + sizeof(BlaiseStrHdr);
    if (len1 > 0) memcpy(dest,        c1, len1);
    if (len2 > 0) memcpy(dest + len1, c2, len2);
    dest[total] = '\0';

    return result;
}
