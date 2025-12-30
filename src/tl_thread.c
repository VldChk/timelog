#include "internal/tl_thread.h"

#if defined(_WIN32)

int tl_mutex_init(tl_mutex_t* mtx) {
    InitializeCriticalSection(mtx);
    return 0;
}

void tl_mutex_destroy(tl_mutex_t* mtx) {
    DeleteCriticalSection(mtx);
}

void tl_mutex_lock(tl_mutex_t* mtx) {
    EnterCriticalSection(mtx);
}

void tl_mutex_unlock(tl_mutex_t* mtx) {
    LeaveCriticalSection(mtx);
}

bool tl_mutex_trylock(tl_mutex_t* mtx) {
    return TryEnterCriticalSection(mtx) != 0;
}

int tl_cond_init(tl_cond_t* cond) {
    InitializeConditionVariable(cond);
    return 0;
}

void tl_cond_destroy(tl_cond_t* cond) {
    /* Windows condition variables don't need explicit destruction */
    (void)cond;
}

void tl_cond_signal(tl_cond_t* cond) {
    WakeConditionVariable(cond);
}

void tl_cond_broadcast(tl_cond_t* cond) {
    WakeAllConditionVariable(cond);
}

void tl_cond_wait(tl_cond_t* cond, tl_mutex_t* mtx) {
    SleepConditionVariableCS(cond, mtx, INFINITE);
}

bool tl_cond_timedwait(tl_cond_t* cond, tl_mutex_t* mtx, uint32_t timeout_ms) {
    return SleepConditionVariableCS(cond, mtx, timeout_ms) != 0;
}

/*
 * Windows thread wrapper.
 * Adapts POSIX-style void* return to Windows DWORD.
 */
typedef struct {
    tl_thread_fn fn;
    void*        arg;
} tl_win_thread_ctx_t;

static DWORD WINAPI tl_win_thread_wrapper(LPVOID param) {
    tl_win_thread_ctx_t* ctx = (tl_win_thread_ctx_t*)param;
    tl_thread_fn fn = ctx->fn;
    void* arg = ctx->arg;

    /* Free context before calling user function (it's on heap) */
    HeapFree(GetProcessHeap(), 0, ctx);

    /* Call user function */
    fn(arg);

    return 0;
}

int tl_thread_create(tl_thread_t* thread, tl_thread_fn fn, void* arg) {
    if (thread == NULL || fn == NULL) return -1;

    /* Allocate context for wrapper */
    tl_win_thread_ctx_t* ctx = (tl_win_thread_ctx_t*)HeapAlloc(
        GetProcessHeap(), 0, sizeof(tl_win_thread_ctx_t));
    if (ctx == NULL) return -1;

    ctx->fn = fn;
    ctx->arg = arg;

    HANDLE h = CreateThread(NULL, 0, tl_win_thread_wrapper, ctx, 0, NULL);
    if (h == NULL) {
        HeapFree(GetProcessHeap(), 0, ctx);
        return -1;
    }

    *thread = h;
    return 0;
}

int tl_thread_join(tl_thread_t thread, void** retval) {
    /* Ignore retval on Windows (we don't capture it) */
    (void)retval;

    if (thread == NULL) return -1;

    DWORD result = WaitForSingleObject(thread, INFINITE);
    if (result != WAIT_OBJECT_0) {
        return -1;
    }

    CloseHandle(thread);
    return 0;
}

#else /* POSIX */

#include <errno.h>
#include <time.h>

int tl_mutex_init(tl_mutex_t* mtx) {
    return pthread_mutex_init(mtx, NULL);
}

void tl_mutex_destroy(tl_mutex_t* mtx) {
    pthread_mutex_destroy(mtx);
}

void tl_mutex_lock(tl_mutex_t* mtx) {
    pthread_mutex_lock(mtx);
}

void tl_mutex_unlock(tl_mutex_t* mtx) {
    pthread_mutex_unlock(mtx);
}

bool tl_mutex_trylock(tl_mutex_t* mtx) {
    return pthread_mutex_trylock(mtx) == 0;
}

int tl_cond_init(tl_cond_t* cond) {
    return pthread_cond_init(cond, NULL);
}

void tl_cond_destroy(tl_cond_t* cond) {
    pthread_cond_destroy(cond);
}

void tl_cond_signal(tl_cond_t* cond) {
    pthread_cond_signal(cond);
}

void tl_cond_broadcast(tl_cond_t* cond) {
    pthread_cond_broadcast(cond);
}

void tl_cond_wait(tl_cond_t* cond, tl_mutex_t* mtx) {
    pthread_cond_wait(cond, mtx);
}

bool tl_cond_timedwait(tl_cond_t* cond, tl_mutex_t* mtx, uint32_t timeout_ms) {
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);

    ts.tv_sec += timeout_ms / 1000;
    ts.tv_nsec += (timeout_ms % 1000) * 1000000;
    if (ts.tv_nsec >= 1000000000) {
        ts.tv_sec += 1;
        ts.tv_nsec -= 1000000000;
    }

    int rc = pthread_cond_timedwait(cond, mtx, &ts);
    return rc == 0;
}

int tl_thread_create(tl_thread_t* thread, tl_thread_fn fn, void* arg) {
    if (thread == NULL || fn == NULL) return -1;
    return pthread_create(thread, NULL, fn, arg);
}

int tl_thread_join(tl_thread_t thread, void** retval) {
    return pthread_join(thread, retval);
}

#endif
