/*
 * Blaise RTL — Exception frame management (Phase 2)
 *
 * Uses setjmp/longjmp for exception dispatch.  Each try block allocates a
 * BlaiseExcFrame on the Pascal stack.  jbuf MUST be at offset 0 so the
 * compiler can pass the frame pointer directly to setjmp.
 *
 * Frame size contract: the compiler allocates BLAISE_EXC_FRAME_ALLOC16 * 16
 * bytes (currently 512) for each try block via QBE alloc16.  This must be >=
 * sizeof(BlaiseExcFrame) on every supported target.
 *
 *   Linux x86_64:  sizeof(jmp_buf) = 200 → frame = 216 bytes  < 512 ✓
 *   macOS ARM64:   sizeof(jmp_buf) ≈ 312 → frame = 328 bytes  < 512 ✓
 */

#include <setjmp.h>
#include <stdlib.h>

typedef struct BlaiseExcFrame {
    jmp_buf jbuf;       /* offset 0 — frame ptr passed directly to setjmp   */
    void*   exception;  /* live exception object; NULL on normal path        */
    void*   prev;       /* previous BlaiseExcFrame* in the thread-local chain */
} BlaiseExcFrame;

#ifdef _WIN32
static __declspec(thread) BlaiseExcFrame* g_exc_top = NULL;
#else
static __thread BlaiseExcFrame* g_exc_top = NULL;
#endif

/*
 * _PushExcFrame — link a new exception frame into the thread-local chain.
 * Called by the compiler BEFORE setjmp at the start of every try block.
 */
void _PushExcFrame(void* frame) {
    BlaiseExcFrame* f = (BlaiseExcFrame*)frame;
    f->exception = NULL;
    f->prev      = (void*)g_exc_top;
    g_exc_top    = f;
}

/*
 * _PopExcFrame — unlink the top frame.
 * Called on normal exit from a try scope or at the start of an except/finally
 * handler before running handler body.
 */
void _PopExcFrame(void) {
    if (g_exc_top)
        g_exc_top = (BlaiseExcFrame*)g_exc_top->prev;
}

/*
 * _Raise — raise an exception.  Sets obj on the current frame and longjmps.
 * Aborts if no active handler exists (unhandled exception).
 */
void _Raise(void* obj) {
    if (!g_exc_top)
        abort();
    g_exc_top->exception = obj;
    longjmp(*(jmp_buf*)g_exc_top, 1);
}

/*
 * _CurrentException — return the live exception object from the current frame.
 * Called from an except/finally handler on the exception path, before
 * _PopExcFrame, to capture the exception pointer for re-raise.
 */
void* _CurrentException(void) {
    return g_exc_top ? g_exc_top->exception : NULL;
}

/*
 * _Reraise — re-raise the given exception to the enclosing handler.
 * Called by the compiler on the exception path of try/finally, after
 * _PopExcFrame has already unlinked the try block's own frame.
 */
void _Reraise(void* exc) {
    _Raise(exc);
}
