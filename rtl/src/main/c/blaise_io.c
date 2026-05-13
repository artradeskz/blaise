/*
 * Blaise — An Object Pascal Compiler
 * Copyright (c) 2026 Graeme Geldenhuys
 * SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
 * Licensed under the Apache License v2.0 with Runtime Library Exception.
 * See LICENSE file in the project root for full license terms.
 *
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

#define _POSIX_C_SOURCE 200809L

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <errno.h>
#include <time.h>

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
/* _GetProcessID() : Integer                                           */
/* Returns the current process ID.                                     */
/* ------------------------------------------------------------------ */

int32_t _GetProcessID(void) {
    return (int32_t)getpid();
}

/* ------------------------------------------------------------------ */
/* _DirectoryExists(Path) : Boolean (0 or 1)                           */
/* Returns 1 if Path exists and is a directory, 0 otherwise.           */
/* ------------------------------------------------------------------ */

int32_t _DirectoryExists(void* path) {
    const char* p = io_str_data(path);
    struct stat st;
    if (stat(p, &st) != 0) return 0;
    return S_ISDIR(st.st_mode) ? 1 : 0;
}

/* ------------------------------------------------------------------ */
/* _GetTempDir() : string                                              */
/* Returns the temp directory (TMPDIR env or /tmp), with trailing '/'. */
/* ------------------------------------------------------------------ */

void* _GetTempDir(void) {
    const char* tmp = getenv("TMPDIR");
    if (!tmp || tmp[0] == '\0') tmp = "/tmp";
    int32_t len = (int32_t)strlen(tmp);
    int need_slash = (len > 0 && tmp[len - 1] != '/') ? 1 : 0;
    void* r = io_str_alloc(len + need_slash);
    memcpy((char*)r, tmp, (size_t)len);
    if (need_slash) ((char*)r)[len] = '/';
    return r;
}

/* ------------------------------------------------------------------ */
/* _GetTempFileName(Dir, Prefix) : string                              */
/* Returns a unique temp file path (like mkstemp).  The file is        */
/* created and immediately closed; caller is responsible for deletion. */

void* _GetTempFileName(void* dir, void* prefix) {
    const char* d  = io_str_data(dir);
    const char* p  = io_str_data(prefix);
    int32_t plen = (int32_t)strlen(p);
    int     fd;
    char*   tmpl;
    int32_t tlen;
    if (strlen(d) == 0) {
        const char* tmp = getenv("TMPDIR");
        if (!tmp || tmp[0] == '\0') tmp = "/tmp";
        int32_t tmplen = (int32_t)strlen(tmp);
        /* template: <tmp>/<prefix>XXXXXX\0 */
        tlen = tmplen + 1 + plen + 6;
        tmpl = (char*)malloc((size_t)(tlen + 1));
        if (!tmpl) return io_str_from_cstr("/tmp/blaise_XXXXXX");
        memcpy(tmpl, tmp, (size_t)tmplen);
        tmpl[tmplen] = '/';
        memcpy(tmpl + tmplen + 1, p, (size_t)plen);
        memcpy(tmpl + tmplen + 1 + plen, "XXXXXX", 6);
        tmpl[tlen] = '\0';
    } else {
        int32_t dlen = (int32_t)strlen(d);
        int need_slash = (d[dlen - 1] != '/') ? 1 : 0;
        /* template: <dir>[/]<prefix>XXXXXX\0 */
        tlen = dlen + need_slash + plen + 6;
        tmpl = (char*)malloc((size_t)(tlen + 1));
        if (!tmpl) return io_str_from_cstr("/tmp/blaise_XXXXXX");
        memcpy(tmpl, d, (size_t)dlen);
        if (need_slash) tmpl[dlen] = '/';
        memcpy(tmpl + dlen + need_slash, p, (size_t)plen);
        memcpy(tmpl + dlen + need_slash + plen, "XXXXXX", 6);
        tmpl[tlen] = '\0';
    }
    fd = mkstemp(tmpl);
    if (fd >= 0) close(fd);
    void* result = io_str_from_cstr(tmpl);
    free(tmpl);
    return result;
}

/* _GetCurrentDir() : string                                           */
/* Returns the current working directory with a trailing '/'.          */
/* ------------------------------------------------------------------ */

void* _GetCurrentDir(void) {
    char buf[4096];
    const char* cwd = getcwd(buf, sizeof(buf));
    if (!cwd) cwd = ".";
    int32_t len = (int32_t)strlen(cwd);
    int need_slash = (len > 0 && cwd[len - 1] != '/') ? 1 : 0;
    void* r = io_str_alloc(len + need_slash);
    memcpy((char*)r, cwd, (size_t)len);
    if (need_slash) ((char*)r)[len] = '/';
    return r;
}

/* ------------------------------------------------------------------ */
/* _ForceDirectories(Path) : Boolean (0 or 1)                          */
/* Creates the directory Path and all parent directories. Returns 1    */
/* on success, 0 on failure. Like mkdir -p.                            */
/* ------------------------------------------------------------------ */

int32_t _ForceDirectories(void* path) {
    const char* p = io_str_data(path);
    if (!p || p[0] == '\0') return 0;

    char buf[4096];
    int32_t len = (int32_t)strlen(p);
    if (len >= (int32_t)sizeof(buf)) return 0;
    memcpy(buf, p, (size_t)len + 1);

    for (int32_t i = 1; i <= len; i++) {
        if (buf[i] == '/' || buf[i] == '\0') {
            char saved = buf[i];
            buf[i] = '\0';
            struct stat st;
            if (stat(buf, &st) != 0) {
                if (mkdir(buf, 0755) != 0 && errno != EEXIST) return 0;
            } else if (!S_ISDIR(st.st_mode)) {
                return 0;
            }
            buf[i] = saved;
        }
    }
    return 1;
}

/* ------------------------------------------------------------------ */
/* _Sleep(Milliseconds)                                                */
/* Suspends execution for the given number of milliseconds.            */
/* ------------------------------------------------------------------ */

void _Sleep(int32_t ms) {
    struct timespec ts;
    ts.tv_sec  = ms / 1000;
    ts.tv_nsec = (ms % 1000) * 1000000L;
    nanosleep(&ts, NULL);
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

/* _ExcludeTrailingPathDelimiter(path) : string
   Removes a trailing '/' if present. */
void* _ExcludeTrailingPathDelimiter(void* path) {
    const char* p   = io_str_data(path);
    int32_t     len = (int32_t)strlen(p);
    if (len > 0 && p[len - 1] == '/') len--;
    void* r = io_str_alloc(len);
    memcpy((char*)r, p, (size_t)len);
    return r;
}

/* _RemoveDir(path) — removes an empty directory (ignores errors). */
void _RemoveDir(void* path) {
    const char* p = io_str_data(path);
    rmdir(p);
}

/* _ExtractFileDir(path) : string
   Returns the directory portion of path WITHOUT the trailing '/'.
   Returns an empty string when path contains no directory separator. */
void* _ExtractFileDir(void* path) {
    const char* p     = io_str_data(path);
    const char* slash = strrchr(p, '/');
    if (!slash || slash == p) return io_str_from_cstr("");
    int32_t len = (int32_t)(slash - p);  /* exclude trailing slash */
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
