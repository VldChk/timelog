#include "tl_sync.h"
#include "tl_locks.h"
#include "tl_log.h"

/*===========================================================================
 * Thread-Local Lock Tracker (Debug Mode Only)
 *===========================================================================*/

#ifdef TL_DEBUG
TL_THREAD_LOCAL tl_lock_tracker_t tl__lock_tracker = {0};
#endif

/*===========================================================================
 * Windows Implementation
 *===========================================================================*/

#if defined(TL_PLATFORM_WINDOWS)

/*---------------------------------------------------------------------------
 * Mutex
 *---------------------------------------------------------------------------*/

tl_status_t tl_mutex_init(tl_mutex_t* mu) {
    TL_ASSERT(mu != NULL);
    InitializeSRWLock(&mu->lock);
#ifdef TL_DEBUG
    mu->owner = 0;
#endif
    return TL_OK;
}

void tl_mutex_destroy(tl_mutex_t* mu) {
    if (mu == NULL) return;
    /* SRWLOCK has no explicit destroy operation. */
#ifdef TL_DEBUG
    TL_ASSERT(mu->owner == 0);
#endif
}

void tl_mutex_lock(tl_mutex_t* mu) {
    TL_ASSERT(mu != NULL);
#ifdef TL_DEBUG
    /* Catch recursive locking: the engine treats all internal mutexes as
     * non-recursive, and SRWLOCK would deadlock if we tried. */
    TL_ASSERT(mu->owner != GetCurrentThreadId());
#endif
    AcquireSRWLockExclusive(&mu->lock);
#ifdef TL_DEBUG
    mu->owner = GetCurrentThreadId();
#endif
}

void tl_mutex_unlock(tl_mutex_t* mu) {
    TL_ASSERT(mu != NULL);
#ifdef TL_DEBUG
    TL_ASSERT(mu->owner == GetCurrentThreadId());
    mu->owner = 0;
#endif
    ReleaseSRWLockExclusive(&mu->lock);
}

bool tl_mutex_trylock(tl_mutex_t* mu) {
    TL_ASSERT(mu != NULL);
#ifdef TL_DEBUG
    TL_ASSERT(mu->owner != GetCurrentThreadId());
#endif
    if (TryAcquireSRWLockExclusive(&mu->lock)) {
#ifdef TL_DEBUG
        mu->owner = GetCurrentThreadId();
#endif
        return true;
    }
    return false;
}

/*---------------------------------------------------------------------------
 * Condition Variable
 *---------------------------------------------------------------------------*/

tl_status_t tl_cond_init(tl_cond_t* cv) {
    TL_ASSERT(cv != NULL);
    InitializeConditionVariable(&cv->cond);
    return TL_OK;
}

void tl_cond_destroy(tl_cond_t* cv) {
    /* CONDITION_VARIABLE has no explicit destroy operation. */
    (void)cv;
}

void tl_cond_wait(tl_cond_t* cv, tl_mutex_t* mu) {
    TL_ASSERT(cv != NULL);
    TL_ASSERT(mu != NULL);
#ifdef TL_DEBUG
    TL_ASSERT(mu->owner == GetCurrentThreadId());
    mu->owner = 0;
#endif
    SleepConditionVariableSRW(&cv->cond, &mu->lock, INFINITE, 0);
#ifdef TL_DEBUG
    mu->owner = GetCurrentThreadId();
#endif
}

bool tl_cond_timedwait(tl_cond_t* cv, tl_mutex_t* mu, uint32_t timeout_ms) {
    TL_ASSERT(cv != NULL);
    TL_ASSERT(mu != NULL);
#ifdef TL_DEBUG
    TL_ASSERT(mu->owner == GetCurrentThreadId());
    mu->owner = 0;
#endif
    BOOL result = SleepConditionVariableSRW(&cv->cond, &mu->lock, timeout_ms, 0);
#ifdef TL_DEBUG
    mu->owner = GetCurrentThreadId();
#endif
    return result != 0;
}

void tl_cond_signal(tl_cond_t* cv) {
    TL_ASSERT(cv != NULL);
    WakeConditionVariable(&cv->cond);
}

/*---------------------------------------------------------------------------
 * Thread
 *
 * Threads are created via _beginthreadex rather than CreateThread because
 * CreateThread does not initialise the CRT's per-thread state. A thread
 * that then uses any libc function (errno, strerror, malloc on some
 * runtimes, etc.) would leak per-thread bookkeeping or crash. The MS
 * recommendation is unambiguous: use _beginthreadex for any thread that
 * may touch the CRT.
 *---------------------------------------------------------------------------*/

#include <process.h>

/* _beginthreadex requires an unsigned __stdcall entry point. */
static unsigned __stdcall win32_thread_wrapper(void* arg) {
    tl_thread_t* t = (tl_thread_t*)arg;
    t->result = t->fn(t->arg);
    return 0;
}

tl_status_t tl_thread_create(tl_thread_t* thread, tl_thread_fn fn, void* arg) {
    TL_ASSERT(thread != NULL);
    TL_ASSERT(fn != NULL);

    thread->fn = fn;
    thread->arg = arg;
    thread->result = NULL;

    /* Note: _beginthreadex signals failure by returning 0, not
     * INVALID_HANDLE_VALUE. */
    uintptr_t h = _beginthreadex(
        NULL,                   /* default security */
        0,                      /* default stack */
        win32_thread_wrapper,
        thread,
        0,                      /* run immediately */
        NULL                    /* discard thread id */
    );

    if (h == 0) {
        return TL_EINTERNAL;
    }
    thread->handle = (HANDLE)h;
    return TL_OK;
}

tl_status_t tl_thread_join(tl_thread_t* thread, void** result) {
    TL_ASSERT(thread != NULL);
    TL_ASSERT(thread->handle != NULL);

    DWORD wait_result = WaitForSingleObject(thread->handle, INFINITE);
    if (wait_result != WAIT_OBJECT_0) {
        /* Even on wait failure the kernel object still needs CloseHandle
         * to release its reference, otherwise the thread leaks. */
        CloseHandle(thread->handle);
        thread->handle = NULL;
        return TL_EINTERNAL;
    }

    CloseHandle(thread->handle);
    thread->handle = NULL;

    if (result != NULL) {
        *result = thread->result;
    }
    return TL_OK;
}

void tl_thread_yield(void) {
    SwitchToThread();
}

void tl_sleep_ms(uint32_t ms) {
    Sleep(ms);
}

uint64_t tl_monotonic_ms(void) {
    /* GetTickCount64 is monotonic milliseconds since boot. The 64-bit
     * counter never wraps in any realistic uptime, and typical resolution
     * is ~15ms which is fine for bounded-wait deadlines. Available since
     * Windows Vista. */
    return GetTickCount64();
}

/*===========================================================================
 * POSIX Implementation
 *===========================================================================*/

#else /* POSIX */

#include <time.h>
#include <sys/time.h>
#include <sched.h>
#include <unistd.h>

/*---------------------------------------------------------------------------
 * POSIX Capability Detection
 *
 * We prefer to pair condition variables with CLOCK_MONOTONIC so timed
 * waits are immune to wall-clock adjustments (NTP slew, manual time
 * changes). This requires pthread_condattr_setclock(), which is only
 * exposed when all three feature macros below are present. Platforms
 * without it (notably older macOS) fall back to CLOCK_REALTIME and
 * accept the risk that a backwards time jump may elongate a wait.
 *---------------------------------------------------------------------------*/
#if defined(_POSIX_CLOCK_SELECTION) && (_POSIX_CLOCK_SELECTION > 0) && \
    defined(CLOCK_MONOTONIC) && defined(_POSIX_MONOTONIC_CLOCK)
    #define TL_HAS_PTHREAD_CONDATTR_SETCLOCK 1
#else
    #define TL_HAS_PTHREAD_CONDATTR_SETCLOCK 0
#endif

/*---------------------------------------------------------------------------
 * Mutex
 *---------------------------------------------------------------------------*/

tl_status_t tl_mutex_init(tl_mutex_t* mu) {
    TL_ASSERT(mu != NULL);

#ifdef TL_DEBUG
    /* ERRORCHECK turns recursive locks and other misuse into immediate
     * errors instead of silent deadlocks — invaluable during development. */
    pthread_mutexattr_t attr;
    pthread_mutexattr_init(&attr);
    pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_ERRORCHECK);

    int rc = pthread_mutex_init(&mu->lock, &attr);
    pthread_mutexattr_destroy(&attr);
#else
    /* Release builds use the default mutex type for minimum overhead. */
    int rc = pthread_mutex_init(&mu->lock, NULL);
#endif

    if (rc != 0) {
        return TL_EINTERNAL;
    }

#ifdef TL_DEBUG
    /* owner is only meaningful while locked == 1, so we leave it
     * uninitialised on purpose. */
    mu->locked = 0;
#endif
    return TL_OK;
}

void tl_mutex_destroy(tl_mutex_t* mu) {
    if (mu == NULL) return;
#ifdef TL_DEBUG
    TL_ASSERT(!mu->locked);
#endif
    pthread_mutex_destroy(&mu->lock);
}

void tl_mutex_lock(tl_mutex_t* mu) {
    TL_ASSERT(mu != NULL);
    int rc = pthread_mutex_lock(&mu->lock);
    /* OS primitive: any failure here would indicate a corrupted mutex
     * (EINVAL) or impossible state; abort rather than risk continuing
     * with a broken lock. */
    TL_VERIFY(rc == 0);
    (void)rc;
#ifdef TL_DEBUG
    mu->owner = pthread_self();
    mu->locked = 1;
#endif
}

void tl_mutex_unlock(tl_mutex_t* mu) {
    TL_ASSERT(mu != NULL);
#ifdef TL_DEBUG
    TL_ASSERT(mu->locked);
    TL_ASSERT(pthread_equal(mu->owner, pthread_self()));
    /* Clear locked first; owner becomes meaningless the moment we drop
     * the lock, and pthread_t cannot be reset to a sentinel. */
    mu->locked = 0;
#endif
    int rc = pthread_mutex_unlock(&mu->lock);
    TL_VERIFY(rc == 0);
    (void)rc;
}

bool tl_mutex_trylock(tl_mutex_t* mu) {
    TL_ASSERT(mu != NULL);
    int rc = pthread_mutex_trylock(&mu->lock);
    if (rc == 0) {
#ifdef TL_DEBUG
        mu->owner = pthread_self();
        mu->locked = 1;
#endif
        return true;
    }
    return false;
}

/*---------------------------------------------------------------------------
 * Condition Variable
 *---------------------------------------------------------------------------*/

tl_status_t tl_cond_init(tl_cond_t* cv) {
    TL_ASSERT(cv != NULL);

#if TL_HAS_PTHREAD_CONDATTR_SETCLOCK
    /* Prefer CLOCK_MONOTONIC; fall back to the default at any error. The
     * use_monotonic flag below records the choice so the matching clock
     * is used when computing absolute timeout values. */
    pthread_condattr_t attr;
    int attr_rc = pthread_condattr_init(&attr);
    int rc;

    if (attr_rc == 0) {
        int setclock_rc = pthread_condattr_setclock(&attr, CLOCK_MONOTONIC);
        if (setclock_rc == 0) {
            rc = pthread_cond_init(&cv->cond, &attr);
            cv->use_monotonic = true;
        } else {
            rc = pthread_cond_init(&cv->cond, NULL);
            cv->use_monotonic = false;
        }
        pthread_condattr_destroy(&attr);
    } else {
        rc = pthread_cond_init(&cv->cond, NULL);
        cv->use_monotonic = false;
    }
#else
    int rc = pthread_cond_init(&cv->cond, NULL);
    cv->use_monotonic = false;
#endif

    if (rc != 0) {
        return TL_EINTERNAL;
    }
    return TL_OK;
}

void tl_cond_destroy(tl_cond_t* cv) {
    if (cv == NULL) return;
    pthread_cond_destroy(&cv->cond);
}

void tl_cond_wait(tl_cond_t* cv, tl_mutex_t* mu) {
    TL_ASSERT(cv != NULL);
    TL_ASSERT(mu != NULL);
#ifdef TL_DEBUG
    TL_ASSERT(mu->locked);
    /* pthread_cond_wait releases the mutex for the duration of the wait,
     * so the debug ownership tracking must reflect that. */
    mu->locked = 0;
#endif
    int rc = pthread_cond_wait(&cv->cond, &mu->lock);
    TL_VERIFY(rc == 0);
    (void)rc;
#ifdef TL_DEBUG
    /* Mutex has been re-acquired on return. */
    mu->owner = pthread_self();
    mu->locked = 1;
#endif
}

bool tl_cond_timedwait(tl_cond_t* cv, tl_mutex_t* mu, uint32_t timeout_ms) {
    TL_ASSERT(cv != NULL);
    TL_ASSERT(mu != NULL);

    struct timespec ts;

    /* Critical correctness requirement: pthread_cond_timedwait interprets
     * the absolute deadline against the clock attached to the condvar.
     * Reading from a different clock here would produce timeouts that are
     * either always immediate (REALTIME ahead of MONOTONIC) or effectively
     * infinite (the reverse). */
#if TL_HAS_PTHREAD_CONDATTR_SETCLOCK
    if (cv->use_monotonic) {
        clock_gettime(CLOCK_MONOTONIC, &ts);
    } else {
        clock_gettime(CLOCK_REALTIME, &ts);
    }
#else
    clock_gettime(CLOCK_REALTIME, &ts);
#endif

    ts.tv_sec += timeout_ms / 1000;
    ts.tv_nsec += (timeout_ms % 1000) * 1000000L;
    if (ts.tv_nsec >= 1000000000L) {
        ts.tv_sec += 1;
        ts.tv_nsec -= 1000000000L;
    }

#ifdef TL_DEBUG
    TL_ASSERT(mu->locked);
    mu->locked = 0;
#endif
    int rc = pthread_cond_timedwait(&cv->cond, &mu->lock, &ts);
#ifdef TL_DEBUG
    mu->owner = pthread_self();
    mu->locked = 1;
#endif

    if (rc == 0) {
        return true;
    }
    if (rc == ETIMEDOUT) {
        return false;
    }
    /* Any other return code (EINVAL, EPERM) indicates a programming bug
     * or a corrupted primitive — neither is recoverable. */
    TL_VERIFY(0);
    return false;
}

void tl_cond_signal(tl_cond_t* cv) {
    TL_ASSERT(cv != NULL);
    pthread_cond_signal(&cv->cond);
}

/*---------------------------------------------------------------------------
 * Thread
 *---------------------------------------------------------------------------*/

tl_status_t tl_thread_create(tl_thread_t* thread, tl_thread_fn fn, void* arg) {
    TL_ASSERT(thread != NULL);
    TL_ASSERT(fn != NULL);

    int rc = pthread_create(&thread->handle, NULL, fn, arg);
    if (rc != 0) {
        thread->valid = false;
        return TL_EINTERNAL;
    }
    thread->valid = true;
    return TL_OK;
}

tl_status_t tl_thread_join(tl_thread_t* thread, void** result) {
    TL_ASSERT(thread != NULL);
    TL_ASSERT(thread->valid);

    void* ret = NULL;
    int rc = pthread_join(thread->handle, &ret);
    if (rc != 0) {
        return TL_EINTERNAL;
    }

    thread->valid = false;

    if (result != NULL) {
        *result = ret;
    }
    return TL_OK;
}

void tl_thread_yield(void) {
    sched_yield();
}

void tl_sleep_ms(uint32_t ms) {
    /*
     * nanosleep over usleep: usleep was removed in POSIX.1-2008, and
     * nanosleep's remaining-time output lets us correctly resume on
     * EINTR rather than sleeping for the full duration again.
     */
    struct timespec ts;
    ts.tv_sec = ms / 1000;
    ts.tv_nsec = (ms % 1000) * 1000000L;

    while (nanosleep(&ts, &ts) == -1 && errno == EINTR) {
        /* Interrupted: resume with the remaining time written by the kernel. */
    }
}

uint64_t tl_monotonic_ms(void) {
    struct timespec ts;
#if defined(CLOCK_MONOTONIC)
    clock_gettime(CLOCK_MONOTONIC, &ts);
#else
    /* Rare fallback when CLOCK_MONOTONIC is unavailable: callers must
     * tolerate the possibility of backwards jumps. */
    clock_gettime(CLOCK_REALTIME, &ts);
#endif
    return (uint64_t)ts.tv_sec * 1000 + (uint64_t)ts.tv_nsec / 1000000;
}

#endif /* Platform selection */
