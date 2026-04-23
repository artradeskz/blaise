/*
 * Blaise RTL — string operation functions
 *
 * String representation (shared with blaise_arc.c):
 *   +--[4 bytes]--+--[4 bytes]--+--[4 bytes]--+--[N bytes]--+--[1 byte]--+
 *   | RefCount    | Length      | Capacity    | UTF-8 data  | NUL        |
 *   +-------------+-------------+-------------+-------------+------------+
 *   ^--- string pointer (header ptr)
 *
 * nil (0) represents an empty / unassigned string.
 * RefCount = -1 marks immortal (statically-allocated) strings.
 *
 * All functions that return a new string allocate a fresh header with
 * RefCount = 0 (unowned). The compiler's ARC wrapper calls _StringAddRef
 * at the assignment site, bringing RefCount to 1.
 */

#include <stdint.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <ctype.h>

#define IMMORTAL_REFCNT (-1)

typedef struct {
    int32_t refcnt;
    int32_t length;
    int32_t capacity;
    /* char data[]; follows immediately */
} BlaiseStrHdr;

/* ------------------------------------------------------------------ */
/* Internal helpers                                                     */
/* ------------------------------------------------------------------ */

static inline BlaiseStrHdr* str_hdr(void* ptr) {
    return (BlaiseStrHdr*)ptr;
}

static inline const char* str_data(void* ptr) {
    return ptr ? (const char*)ptr + sizeof(BlaiseStrHdr) : "";
}

static inline int32_t str_len(void* ptr) {
    return ptr ? str_hdr(ptr)->length : 0;
}

/* Allocate a new Blaise string of exactly `len` bytes (plus NUL).
   RefCount is set to 0 (unowned); caller must call _StringAddRef. */
static void* str_alloc(int32_t len) {
    BlaiseStrHdr* h = (BlaiseStrHdr*)malloc(sizeof(BlaiseStrHdr) + len + 1);
    if (!h) return NULL;
    h->refcnt   = 0;
    h->length   = len;
    h->capacity = len;
    ((char*)(h + 1))[len] = '\0';
    return (void*)h;
}

/* ------------------------------------------------------------------ */
/* _StringLength(s) : Integer                                           */
/* ------------------------------------------------------------------ */

int32_t _StringLength(void* s) {
    return str_len(s);
}

/* ------------------------------------------------------------------ */
/* _StringPos(sub, s) : Integer  — 1-based; 0 if not found            */
/* ------------------------------------------------------------------ */

int32_t _StringPos(void* sub, void* s) {
    const char* haystack = str_data(s);
    const char* needle   = str_data(sub);
    int32_t     nlen     = str_len(sub);

    if (nlen == 0) return 1;  /* empty needle is always at position 1 */

    const char* found = strstr(haystack, needle);
    if (!found) return 0;
    return (int32_t)(found - haystack) + 1;  /* convert to 1-based */
}

/* ------------------------------------------------------------------ */
/* _StringCopy(s, from, count) : string  — 1-based from               */
/* ------------------------------------------------------------------ */

void* _StringCopy(void* s, int32_t from, int32_t count) {
    int32_t     slen = str_len(s);
    const char* data = str_data(s);

    /* Clamp to valid range (1-based indexing, Delphi semantics) */
    if (from < 1) from = 1;
    int32_t start = from - 1;  /* 0-based offset */
    if (start >= slen) {
        /* Return empty string */
        return str_alloc(0);
    }
    if (count < 0) count = 0;
    if (start + count > slen) count = slen - start;

    void* result = str_alloc(count);
    if (result && count > 0)
        memcpy((char*)result + sizeof(BlaiseStrHdr), data + start, count);
    return result;
}

/* ------------------------------------------------------------------ */
/* _StringUpperCase(s) : string                                         */
/* ------------------------------------------------------------------ */

void* _StringUpperCase(void* s) {
    int32_t     len  = str_len(s);
    const char* data = str_data(s);
    void*       r    = str_alloc(len);
    if (!r) return NULL;
    char* dst = (char*)r + sizeof(BlaiseStrHdr);
    for (int32_t i = 0; i < len; i++)
        dst[i] = (char)toupper((unsigned char)data[i]);
    return r;
}

/* ------------------------------------------------------------------ */
/* _StringLowerCase(s) : string                                         */
/* ------------------------------------------------------------------ */

void* _StringLowerCase(void* s) {
    int32_t     len  = str_len(s);
    const char* data = str_data(s);
    void*       r    = str_alloc(len);
    if (!r) return NULL;
    char* dst = (char*)r + sizeof(BlaiseStrHdr);
    for (int32_t i = 0; i < len; i++)
        dst[i] = (char)tolower((unsigned char)data[i]);
    return r;
}

/* ------------------------------------------------------------------ */
/* _StringSameText(s1, s2) : Boolean (0 or 1)                          */
/* ------------------------------------------------------------------ */

int32_t _StringSameText(void* s1, void* s2) {
    int32_t     len1 = str_len(s1);
    int32_t     len2 = str_len(s2);
    const char* d1   = str_data(s1);
    const char* d2   = str_data(s2);
    int32_t     i;

    if (len1 != len2) return 0;
    for (i = 0; i < len1; i++) {
        if (tolower((unsigned char)d1[i]) != tolower((unsigned char)d2[i]))
            return 0;
    }
    return 1;
}

/* ------------------------------------------------------------------ */
/* _IntToStr(n) : string                                                */
/* ------------------------------------------------------------------ */

void* _IntToStr(int32_t n) {
    char buf[24];
    int  written = snprintf(buf, sizeof(buf), "%d", n);
    if (written < 0) written = 0;
    void* r = str_alloc(written);
    if (r && written > 0)
        memcpy((char*)r + sizeof(BlaiseStrHdr), buf, written);
    return r;
}

/* ------------------------------------------------------------------ */
/* _StrToInt(s) : Integer                                               */
/* ------------------------------------------------------------------ */

int32_t _StrToInt(void* s) {
    const char* data = str_data(s);
    return (int32_t)strtol(data, NULL, 10);
}

/* ------------------------------------------------------------------ */
/* _StringFormat(fmt, ...) : string                                     */
/*                                                                      */
/* Variadic: after the format string pointer, each format argument      */
/* is passed as a (tag: int, value: int or void*) pair:                 */
/*   tag=0 → int32 value (matched to %d in format)                     */
/*   tag=1 → void* Blaise string (matched to %s in format)             */
/*                                                                      */
/* Scans the format string for %d and %s specifiers, consuming one     */
/* (tag, value) pair per specifier.  %% is emitted as a literal %.     */
/* ------------------------------------------------------------------ */

void* _StringFormat(void* fmt, ...) {
    const char* f    = str_data(fmt);
    int         flen = str_len(fmt);

    /* Two-pass: compute output length, then fill buffer. */
    va_list ap1, ap2;
    va_start(ap1, fmt);
    va_copy(ap2, ap1);

    /* Pass 1: compute total output length */
    size_t out_len = 0;
    const char* p  = f;
    const char* end = f + flen;
    while (p < end) {
        if (*p == '%' && p + 1 < end) {
            p++;
            if (*p == 'd') {
                int tag = va_arg(ap1, int);
                if (tag == 0) {
                    int32_t v = (int32_t)va_arg(ap1, int);
                    char tmp[24];
                    out_len += (size_t)snprintf(tmp, sizeof(tmp), "%d", v);
                } else {
                    void* sv = va_arg(ap1, void*);
                    out_len += (size_t)str_len(sv);
                }
                p++;
            } else if (*p == 's') {
                int tag = va_arg(ap1, int);
                if (tag == 1) {
                    void* sv = va_arg(ap1, void*);
                    out_len += (size_t)str_len(sv);
                } else {
                    int32_t v = (int32_t)va_arg(ap1, int);
                    char tmp[24];
                    out_len += (size_t)snprintf(tmp, sizeof(tmp), "%d", v);
                }
                p++;
            } else if (*p == '%') {
                out_len++;
                p++;
            } else {
                out_len++;  /* unknown %x: emit as-is */
                out_len++;
                p++;
            }
        } else {
            out_len++;
            p++;
        }
    }
    va_end(ap1);

    /* Allocate result string */
    void* result = str_alloc((int32_t)out_len);
    if (!result) { va_end(ap2); return NULL; }
    char* dst = (char*)result + sizeof(BlaiseStrHdr);

    /* Pass 2: fill buffer */
    p = f;
    while (p < end) {
        if (*p == '%' && p + 1 < end) {
            p++;
            if (*p == 'd') {
                int tag = va_arg(ap2, int);
                int32_t v;
                if (tag == 0)
                    v = (int32_t)va_arg(ap2, int);
                else {
                    void* sv = va_arg(ap2, void*);
                    v = 0; (void)sv;
                }
                dst += sprintf(dst, "%d", v);
                p++;
            } else if (*p == 's') {
                int tag = va_arg(ap2, int);
                if (tag == 1) {
                    void* sv = va_arg(ap2, void*);
                    int32_t slen = str_len(sv);
                    if (slen > 0)
                        memcpy(dst, str_data(sv), (size_t)slen);
                    dst += slen;
                } else {
                    int32_t v = (int32_t)va_arg(ap2, int);
                    dst += sprintf(dst, "%d", v);
                }
                p++;
            } else if (*p == '%') {
                *dst++ = '%';
                p++;
            } else {
                *dst++ = '%';
                *dst++ = *p++;
            }
        } else {
            *dst++ = *p++;
        }
    }
    va_end(ap2);
    *dst = '\0';
    return result;
}
