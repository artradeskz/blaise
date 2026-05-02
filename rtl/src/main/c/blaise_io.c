/*
 * Blaise RTL — file I/O, CLI, and process primitives
 *
 * All functions that return a Blaise string allocate a fresh header with
 * RefCount = 0 (unowned). The compiler's ARC wrapper calls _StringAddRef
 * at the assignment site.
 *
 * String representation (shared with blaise_str.c):
 *   +--[4 bytes]--+--[4 bytes]--+--[4 bytes]--+--[N bytes]--+--[1 byte]--+
 *   | RefCount    | Length      | Capacity    | UTF-8 data  | NUL        |
 *   +-------------+-------------+-------------+-------------+------------+
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* ------------------------------------------------------------------ */
/* String helpers — data-pointer convention.
   Variable slots hold a pointer to the char data; the 12-byte header
   (refcount, length, capacity) lives immediately before it at offsets
   data_ptr-12, data_ptr-8, data_ptr-4 respectively.              */
/* ------------------------------------------------------------------ */

#define BLAISE_STR_HDR 12   /* sizeof(refcount + length + capacity) */

static inline const char* io_str_data(void* data_ptr) {
    return data_ptr ? (const char*)data_ptr : "";
}

static inline int32_t io_str_len(void* data_ptr) {
    return data_ptr ? ((int32_t*)data_ptr)[-2] : 0;  /* length at -8 */
}

static void* io_str_alloc(int32_t len) {
    char* base = (char*)malloc((size_t)(BLAISE_STR_HDR + len + 1));
    if (!base) return NULL;
    ((int32_t*)base)[0] = 0;    /* refcount  */
    ((int32_t*)base)[1] = len;  /* length    */
    ((int32_t*)base)[2] = len;  /* capacity  */
    base[BLAISE_STR_HDR + len]  = '\0';
    return base + BLAISE_STR_HDR;  /* DATA POINTER */
}

/* Build a Blaise string from a C string (may be NULL → empty). */
static void* io_str_from_cstr(const char* s) {
    int32_t len = s ? (int32_t)strlen(s) : 0;
    void*   r   = io_str_alloc(len);
    if (r && len > 0)
        memcpy((char*)r, s, (size_t)len);   /* data IS r */
    return r;
}

/* ------------------------------------------------------------------ */
/* Global argc / argv — set by _SetArgs before Blaise main runs       */
/* ------------------------------------------------------------------ */

static int    g_argc = 0;
static char** g_argv = NULL;

void _SetArgs(int32_t argc, char** argv) {
    g_argc = (int)argc;
    g_argv = argv;
}

/* ------------------------------------------------------------------ */
/* _ParamCount() : Integer                                              */
/* Returns the number of command-line arguments (excluding program).   */
/* ------------------------------------------------------------------ */

int32_t _ParamCount(void) {
    return g_argc > 0 ? g_argc - 1 : 0;
}

/* ------------------------------------------------------------------ */
/* _ParamStr(Index) : string                                            */
/* 0 = program name; 1..ParamCount = arguments.                        */
/* ------------------------------------------------------------------ */

void* _ParamStr(int32_t index) {
    if (g_argv == NULL || index < 0 || index >= g_argc)
        return io_str_from_cstr("");
    return io_str_from_cstr(g_argv[index]);
}

/* ------------------------------------------------------------------ */
/* _ReadFile(FileName) : string                                         */
/* Reads the entire file into a Blaise string. Returns empty on error. */
/* ------------------------------------------------------------------ */

void* _ReadFile(void* filename) {
    const char* path = io_str_data(filename);
    FILE*       f    = fopen(path, "rb");
    if (!f) return io_str_from_cstr("");

    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    rewind(f);

    if (sz < 0) { fclose(f); return io_str_from_cstr(""); }

    void* r = io_str_alloc((int32_t)sz);
    if (!r) { fclose(f); return NULL; }

    size_t n = fread((char*)r, 1, (size_t)sz, f);  /* r IS the data pointer */
    fclose(f);
    ((int32_t*)r)[-2] = (int32_t)n;  /* patch length  at data_ptr-8 */
    ((int32_t*)r)[-1] = (int32_t)n;  /* patch capacity at data_ptr-4 */
    ((char*)r)[n]     = '\0';
    return r;
}

/* ------------------------------------------------------------------ */
/* _WriteFile(FileName, Content)                                        */
/* Writes (overwrites) a Blaise string to a file.                      */
/* ------------------------------------------------------------------ */

void _WriteFile(void* filename, void* content) {
    const char* path = io_str_data(filename);
    int32_t     len  = io_str_len(content);
    const char* data = io_str_data(content);
    FILE*       f    = fopen(path, "wb");
    if (!f) return;
    if (len > 0) fwrite(data, 1, (size_t)len, f);
    fclose(f);
}

/* ------------------------------------------------------------------ */
/* _AppendFile(FileName, Content)                                       */
/* Appends a Blaise string to a file.                                  */
/* ------------------------------------------------------------------ */

void _AppendFile(void* filename, void* content) {
    const char* path = io_str_data(filename);
    int32_t     len  = io_str_len(content);
    const char* data = io_str_data(content);
    FILE*       f    = fopen(path, "ab");
    if (!f) return;
    if (len > 0) fwrite(data, 1, (size_t)len, f);
    fclose(f);
}

/* ------------------------------------------------------------------ */
/* _FileExists(FileName) : Boolean (0 or 1)                            */
/* ------------------------------------------------------------------ */

int32_t _FileExists(void* filename) {
    const char* path = io_str_data(filename);
    FILE*       f    = fopen(path, "rb");
    if (!f) return 0;
    fclose(f);
    return 1;
}

/* ------------------------------------------------------------------ */
/* _DeleteFile(FileName) : void                                         */
/* Deletes a file. Silently ignores failure.                            */
/* ------------------------------------------------------------------ */

void _DeleteFile(void* filename) {
    const char* path = io_str_data(filename);
    remove(path);
}

/* ------------------------------------------------------------------ */
/* _GetEnvVar(Name) : string                                            */
/* Returns the value of environment variable Name, or empty string.    */
/* ------------------------------------------------------------------ */

void* _GetEnvVar(void* name) {
    const char* key = io_str_data(name);
    const char* val = getenv(key);
    return io_str_from_cstr(val ? val : "");
}

/* ------------------------------------------------------------------ */
/* _Exec(Command) : Integer                                             */
/* Runs a shell command via system(). Returns exit status.             */
/* ------------------------------------------------------------------ */

int32_t _Exec(void* cmd) {
    const char* s = io_str_data(cmd);
    int rc = system(s);
#ifdef WEXITSTATUS
    if (rc != -1 && WIFEXITED(rc)) rc = WEXITSTATUS(rc);
#endif
    return (int32_t)rc;
}

/* ------------------------------------------------------------------ */
/* _Halt(ExitCode)                                                      */
/* ------------------------------------------------------------------ */

void _Halt(int32_t code) {
    exit((int)code);
}

/* ------------------------------------------------------------------ */
/* File-path manipulation (SysUtils equivalents)                       */
/* ------------------------------------------------------------------ */

/* _ChangeFileExt(path, ext) : string
   Replaces the extension of path with ext.  ext should include the
   leading dot (e.g. ".bak"), or be empty to strip the extension.
   Only the last dot in the base-name (after the last '/') is replaced. */
void* _ChangeFileExt(void* path, void* ext) {
    const char* p    = io_str_data(path);
    const char* e    = io_str_data(ext);
    const char* slash = strrchr(p, '/');
    const char* base  = slash ? slash + 1 : p;
    const char* dot   = strrchr(base, '.');
    int32_t stem_len  = dot ? (int32_t)(dot - p) : (int32_t)strlen(p);
    int32_t ext_len   = (int32_t)strlen(e);
    void*   r         = io_str_alloc(stem_len + ext_len);
    memcpy((char*)r,            p, (size_t)stem_len);
    memcpy((char*)r + stem_len, e, (size_t)ext_len);
    return r;
}

/* _ExtractFileName(path) : string
   Returns the filename portion of path (everything after the last '/'). */
void* _ExtractFileName(void* path) {
    const char* p     = io_str_data(path);
    const char* slash = strrchr(p, '/');
    return io_str_from_cstr(slash ? slash + 1 : p);
}

/* _ExtractFilePath(path) : string
   Returns the directory portion of path including the trailing '/'.
   Returns an empty string when path contains no directory separator. */
void* _ExtractFilePath(void* path) {
    const char* p     = io_str_data(path);
    const char* slash = strrchr(p, '/');
    if (!slash) return io_str_from_cstr("");
    int32_t len = (int32_t)(slash - p + 1);
    void*   r   = io_str_alloc(len);
    memcpy((char*)r, p, (size_t)len);
    return r;
}

/* _IncludeTrailingPathDelimiter(path) : string
   Ensures path ends with '/'.  Returns path unchanged if it already does. */
void* _IncludeTrailingPathDelimiter(void* path) {
    const char* p   = io_str_data(path);
    int32_t     len = (int32_t)strlen(p);
    if (len > 0 && p[len - 1] == '/') return io_str_from_cstr(p);
    void* r   = io_str_alloc(len + 1);
    memcpy((char*)r, p, (size_t)len);
    ((char*)r)[len] = '/';
    return r;
}
