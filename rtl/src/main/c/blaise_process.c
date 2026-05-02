/*
 * Blaise RTL — process management
 *
 * Provides fork/exec/pipe helpers used by Process.pas's TProcess class.
 * Each _ProcessCreate() call allocates an independent BlaiseProcess struct
 * that can be configured, executed, and freed independently, supporting
 * concurrent or sequential subprocess launches.
 *
 * String representation (shared with blaise_str.c / blaise_io.c):
 *   +--[4 bytes]--+--[4 bytes]--+--[4 bytes]--+--[N bytes]--+--[1 byte]--+
 *   | RefCount    | Length      | Capacity    | UTF-8 data  | NUL        |
 *   +-------------+-------------+-------------+-------------+------------+
 *
 * Windows: not yet supported; _ProcessExecute() is a no-op stub.
 */

#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#ifndef _WIN32
#  include <unistd.h>
#  include <sys/types.h>
#  include <sys/wait.h>
#  include <errno.h>
#endif

/* ------------------------------------------------------------------ */
/* String helpers — data-pointer convention (mirrors blaise_str.pas)   */
/* Variable slots hold pointer to char data; header lives before it.   */
/* ------------------------------------------------------------------ */

#define BLAISE_STR_HDR 12   /* refcount + length + capacity */

static inline const char* proc_str_data(void* data_ptr) {
    return data_ptr ? (const char*)data_ptr : "";
}

static void* proc_str_alloc(int32_t len) {
    char* base = (char*)malloc((size_t)(BLAISE_STR_HDR + len + 1));
    if (!base) return NULL;
    ((int32_t*)base)[0] = 0;    /* refcount  */
    ((int32_t*)base)[1] = len;  /* length    */
    ((int32_t*)base)[2] = len;  /* capacity  */
    base[BLAISE_STR_HDR + len]  = '\0';
    return base + BLAISE_STR_HDR;  /* DATA POINTER */
}

static void* proc_str_from_cstr(const char* s) {
    int32_t len = s ? (int32_t)strlen(s) : 0;
    void*   r   = proc_str_alloc(len);
    if (r && len > 0)
        memcpy((char*)r, s, (size_t)len);   /* data IS r */
    return r;
}

/* ------------------------------------------------------------------ */
/* BlaiseProcess struct                                                 */
/* ------------------------------------------------------------------ */

typedef struct {
    char*   exe;
    char**  argv;       /* NULL-terminated, argv[0] = exe */
    int     argc;
    int     argv_cap;
#ifndef _WIN32
    pid_t   pid;
    int     pipe_fd;    /* read end of stdout+stderr pipe; -1 if closed */
    int     exit_code;
    int     waited;     /* 1 after waitpid reaped the child */
#endif
} BlaiseProcess;

/* ------------------------------------------------------------------ */
/* _ProcessCreate() : Pointer                                           */
/* Allocates and zero-initialises a BlaiseProcess struct.              */
/* ------------------------------------------------------------------ */

void* _ProcessCreate(void) {
    BlaiseProcess* p = (BlaiseProcess*)calloc(1, sizeof(BlaiseProcess));
#ifndef _WIN32
    if (p) p->pipe_fd = -1;
#endif
    return (void*)p;
}

/* ------------------------------------------------------------------ */
/* _ProcessSetExe(p, exe)                                              */
/* Sets the executable path.                                           */
/* ------------------------------------------------------------------ */

void _ProcessSetExe(void* proc, void* exe_str) {
    BlaiseProcess* p = (BlaiseProcess*)proc;
    free(p->exe);
    p->exe = strdup(proc_str_data(exe_str));
}

/* ------------------------------------------------------------------ */
/* _ProcessAddArg(p, arg)                                              */
/* Appends one argument.  argv[0] is set to exe at Execute time.      */
/* ------------------------------------------------------------------ */

void _ProcessAddArg(void* proc, void* arg_str) {
    BlaiseProcess* p   = (BlaiseProcess*)proc;
    const char*    arg = proc_str_data(arg_str);

    /* grow argv (leave room for argv[0]=exe and final NULL) */
    if (p->argc + 2 >= p->argv_cap) {
        int new_cap = p->argv_cap == 0 ? 8 : p->argv_cap * 2;
        char** new_argv = (char**)realloc(p->argv, (size_t)new_cap * sizeof(char*));
        if (!new_argv) return;
        p->argv     = new_argv;
        p->argv_cap = new_cap;
    }
    p->argv[p->argc++] = strdup(arg);
}

/* ------------------------------------------------------------------ */
/* _ProcessExecute(p)                                                  */
/* Forks the child with stdout+stderr redirected to a pipe.           */
/* The parent holds the read end; the child execs the program.        */
/* ------------------------------------------------------------------ */

void _ProcessExecute(void* proc) {
#ifdef _WIN32
    (void)proc;  /* stub */
#else
    BlaiseProcess* p = (BlaiseProcess*)proc;
    int fds[2];

    if (pipe(fds) < 0) return;

    /* Build argv: [exe, arg1, ..., argN, NULL] */
    int total = p->argc + 2;  /* +1 for exe slot, +1 for NULL */
    char** argv = (char**)malloc((size_t)total * sizeof(char*));
    if (!argv) { close(fds[0]); close(fds[1]); return; }
    argv[0] = p->exe ? p->exe : (char*)"";
    int i;
    for (i = 0; i < p->argc; i++) argv[i + 1] = p->argv[i];
    argv[total - 1] = NULL;

    pid_t pid = fork();
    if (pid < 0) {
        free(argv);
        close(fds[0]);
        close(fds[1]);
        return;
    }

    if (pid == 0) {
        /* child: wire stdout and stderr to write end of pipe */
        close(fds[0]);
        dup2(fds[1], STDOUT_FILENO);
        dup2(fds[1], STDERR_FILENO);
        close(fds[1]);
        execvp(argv[0], argv);
        /* exec failed */
        _exit(127);
    }

    /* parent */
    free(argv);
    close(fds[1]);
    p->pid     = pid;
    p->pipe_fd = fds[0];
    p->waited  = 0;
#endif
}

/* ------------------------------------------------------------------ */
/* _ProcessRunning(p) : Integer (Boolean)                              */
/* Non-blocking check: returns 1 if child is still alive, 0 if done. */
/* ------------------------------------------------------------------ */

int32_t _ProcessRunning(void* proc) {
#ifdef _WIN32
    (void)proc;
    return 0;
#else
    BlaiseProcess* p = (BlaiseProcess*)proc;
    if (p->waited || p->pid == 0) return 0;
    int status;
    pid_t r = waitpid(p->pid, &status, WNOHANG);
    if (r == p->pid) {
        p->exit_code = WIFEXITED(status) ? WEXITSTATUS(status) : 1;
        p->waited    = 1;
        return 0;
    }
    return r == 0 ? 1 : 0;
#endif
}

/* ------------------------------------------------------------------ */
/* _ProcessReadOutput(p) : string                                       */
/* Blocking read: returns the next chunk of output (up to 4 KiB).    */
/* Returns an empty Blaise string on EOF (child finished writing).    */
/* ------------------------------------------------------------------ */

void* _ProcessReadOutput(void* proc) {
#ifdef _WIN32
    (void)proc;
    return proc_str_from_cstr("");
#else
    BlaiseProcess* p = (BlaiseProcess*)proc;
    if (p->pipe_fd < 0) return proc_str_from_cstr("");

    char buf[4096];
    ssize_t n = read(p->pipe_fd, buf, sizeof(buf));
    if (n <= 0) {
        close(p->pipe_fd);
        p->pipe_fd = -1;
        return proc_str_from_cstr("");
    }
    void* r = proc_str_alloc((int32_t)n);
    if (r) memcpy((char*)r, buf, (size_t)n);   /* data IS r */
    return r;
#endif
}

/* ------------------------------------------------------------------ */
/* _ProcessWaitOnExit(p)                                               */
/* Blocks until the child exits and reaps it.                         */
/* ------------------------------------------------------------------ */

void _ProcessWaitOnExit(void* proc) {
#ifndef _WIN32
    BlaiseProcess* p = (BlaiseProcess*)proc;
    if (p->waited || p->pid == 0) return;
    int status;
    waitpid(p->pid, &status, 0);
    p->exit_code = WIFEXITED(status) ? WEXITSTATUS(status) : 1;
    p->waited    = 1;
#endif
}

/* ------------------------------------------------------------------ */
/* _ProcessExitCode(p) : Integer                                        */
/* Returns the exit code (call after WaitOnExit).                     */
/* ------------------------------------------------------------------ */

int32_t _ProcessExitCode(void* proc) {
#ifdef _WIN32
    (void)proc;
    return 0;
#else
    BlaiseProcess* p = (BlaiseProcess*)proc;
    return (int32_t)p->exit_code;
#endif
}

/* ------------------------------------------------------------------ */
/* _ProcessFree(p)                                                      */
/* Frees the struct, its exe string, and all argv strings.            */
/* ------------------------------------------------------------------ */

void _ProcessFree(void* proc) {
#ifndef _WIN32
    BlaiseProcess* p = (BlaiseProcess*)proc;
    if (!p) return;
    if (p->pipe_fd >= 0) close(p->pipe_fd);
    free(p->exe);
    int i;
    for (i = 0; i < p->argc; i++) free(p->argv[i]);
    free(p->argv);
    free(p);
#else
    free(proc);
#endif
}
