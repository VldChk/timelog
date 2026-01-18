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
    /* SRWLock doesn't require explicit destruction */
#ifdef TL_DEBUG
    TL_ASSERT(mu->owner == 0);
#endif
}

void tl_mutex_lock(tl_mutex_t* mu) {
    TL_ASSERT(mu != NULL);
#ifdef TL_DEBUG
    TL_ASSERT(mu->owner != GetCurrentThreadId()); /* Detect recursive lock */
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
    TL_ASSERT(mu->owner != GetCurrentThreadId()); /* Detect recursive lock */
#endif
    if (TryAcquireSRWLockExclusive(&mu->lock)) {
#ifdef TL_DEBUG
        mu->owner = GetCurrentThreadId();
#endif
        return true;
    }
    return false;
}

#ifdef TL_DEBUG
bool tl_mutex_is_held(const tl_mutex_t* mu) {
    return mu && mu->owner == GetCurrentThreadId();
}
#endif

/*---------------------------------------------------------------------------
 * Condition Variable
 *---------------------------------------------------------------------------*/

tl_status_t tl_cond_init(tl_cond_t* cv) {
    TL_ASSERT(cv != NULL);
    InitializeConditionVariable(&cv->cond);
    return TL_OK;
}

void tl_cond_destroy(tl_cond_t* cv) {
    /* CONDITION_VARIABLE doesn't require explicit destruction */
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

void tl_cond_broadcast(tl_cond_t* cv) {
    TL_ASSERT(cv != NULL);
    WakeAllConditionVariable(&cv->cond);
}

/*---------------------------------------------------------------------------
 * Thread
 *
 * IMPORTANT: We use _beginthreadex instead of CreateThread.
 * CreateThread does not initialize CRT per-thread data, which causes:
 * - Memory leaks if the thread uses CRT functions
 * - Potential crashes with errno, strerror, etc.
 * _beginthreadex properly initializes the CRT and is the recommended API.
 *---------------------------------------------------------------------------*/

#include <process.h>  /* For _beginthreadex */

/* Windows thread wrapper - uses unsigned __stdcall for _beginthreadex */
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

    /* _beginthreadex returns handle or 0 on error (not INVALID_HANDLE_VALUE) */
    uintptr_t h = _beginthreadex(
        NULL,                   /* default security attributes */
        0,                      /* default stack size */
        win32_thread_wrapper,
        thread,
        0,                      /* run immediately */
        NULL                    /* don't need thread ID */
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
        /* Close handle even on error to prevent resource leak */
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

uint64_t tl_thread_self_id(void) {
    return (uint64_t)GetCurrentThreadId();
}

#ifdef TL_DEBUG
/*
 * Thread-safe one-time initialization for SetThreadDescription.
 * Uses InitOnceExecuteOnce to avoid data races when multiple threads
 * call tl_thread_set_name() concurrently at startup.
 */
typedef HRESULT (WINAPI *SetThreadDescriptionFn)(HANDLE, PCWSTR);

static INIT_ONCE g_thread_name_init_once = INIT_ONCE_STATIC_INIT;
static SetThreadDescriptionFn g_set_thread_desc_fn = NULL;

static BOOL CALLBACK thread_name_init_callback(
    PINIT_ONCE init_once,
    PVOID parameter,
    PVOID* context)
{
    (void)init_once;
    (void)parameter;
    (void)context;

    HMODULE kernel32 = GetModuleHandleW(L"kernel32.dll");
    if (kernel32) {
        g_set_thread_desc_fn = (SetThreadDescriptionFn)GetProcAddress(
            kernel32, "SetThreadDescription");
    }
    return TRUE;
}

void tl_thread_set_name(const char* name) {
    if (name == NULL) return;

    /*
     * SetThreadDescription requires Windows 10 1607+.
     * We dynamically load it to avoid breaking older systems.
     * InitOnceExecuteOnce ensures thread-safe one-time initialization.
     */
    InitOnceExecuteOnce(&g_thread_name_init_once, thread_name_init_callback, NULL, NULL);

    if (g_set_thread_desc_fn) {
        /* Convert to wide string (simple ASCII conversion sufficient for thread names) */
        wchar_t wname[64];
        int i = 0;
        while (i < 63 && name[i]) {  /* Check bounds before array access */
            wname[i] = (wchar_t)(unsigned char)name[i];
            i++;
        }
        wname[i] = L'\0';
        g_set_thread_desc_fn(GetCurrentThread(), wname);
    }
}
#endif

void tl_thread_yield(void) {
    SwitchToThread();
}

void tl_sleep_ms(uint32_t ms) {
    Sleep(ms);
}

uint64_t tl_monotonic_ms(void) {
    /* GetTickCount64 returns milliseconds since system start.
     * Available on Windows Vista and later (our minimum target).
     * Never wraps (64-bit), monotonic, ~15ms resolution typical. */
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
#include <string.h>

/*---------------------------------------------------------------------------
 * POSIX Capability Detection
 *
 * pthread_condattr_setclock() is required to use CLOCK_MONOTONIC with
 * condition variables. It's available when:
 * - _POSIX_CLOCK_SELECTION is defined and > 0
 * - CLOCK_MONOTONIC is defined
 * - _POSIX_MONOTONIC_CLOCK is defined
 *
 * On systems where setclock isn't available (e.g., older macOS), we fall
 * back to CLOCK_REALTIME which can have issues with time jumps.
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
    /* Use ERRORCHECK in debug mode for deadlock detection */
    pthread_mutexattr_t attr;
    pthread_mutexattr_init(&attr);
    pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_ERRORCHECK);

    int rc = pthread_mutex_init(&mu->lock, &attr);
    pthread_mutexattr_destroy(&attr);
#else
    /* Use default (faster) mutex in release mode */
    int rc = pthread_mutex_init(&mu->lock, NULL);
#endif

    if (rc != 0) {
        return TL_EINTERNAL;
    }

#ifdef TL_DEBUG
    /* Note: We don't initialize owner since it's only valid when locked == 1 */
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
    TL_ASSERT(rc == 0);
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
    /* Clear locked flag first - owner is now invalid */
    mu->locked = 0;
    /* Note: We don't clear owner since pthread_t is opaque */
#endif
    int rc = pthread_mutex_unlock(&mu->lock);
    TL_ASSERT(rc == 0);
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

#ifdef TL_DEBUG
bool tl_mutex_is_held(const tl_mutex_t* mu) {
    return mu && mu->locked && pthread_equal(mu->owner, pthread_self());
}
#endif

/*---------------------------------------------------------------------------
 * Condition Variable
 *---------------------------------------------------------------------------*/

tl_status_t tl_cond_init(tl_cond_t* cv) {
    TL_ASSERT(cv != NULL);

#if TL_HAS_PTHREAD_CONDATTR_SETCLOCK
    /* Use CLOCK_MONOTONIC for reliable timeouts */
    pthread_condattr_t attr;
    int attr_rc = pthread_condattr_init(&attr);
    int rc;

    if (attr_rc == 0) {
        int setclock_rc = pthread_condattr_setclock(&attr, CLOCK_MONOTONIC);
        if (setclock_rc == 0) {
            rc = pthread_cond_init(&cv->cond, &attr);
            cv->use_monotonic = true;
        } else {
            /* setclock failed, fall back to default (CLOCK_REALTIME) */
            rc = pthread_cond_init(&cv->cond, NULL);
            cv->use_monotonic = false;
        }
        pthread_condattr_destroy(&attr);
    } else {
        /* attr init failed, fall back to default */
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
    /* Mark as unlocked before wait (mutex will be released during wait) */
    mu->locked = 0;
#endif
    int rc = pthread_cond_wait(&cv->cond, &mu->lock);
    TL_ASSERT(rc == 0);
    (void)rc;
#ifdef TL_DEBUG
    /* Mutex is reacquired after wait */
    mu->owner = pthread_self();
    mu->locked = 1;
#endif
}

bool tl_cond_timedwait(tl_cond_t* cv, tl_mutex_t* mu, uint32_t timeout_ms) {
    TL_ASSERT(cv != NULL);
    TL_ASSERT(mu != NULL);

    struct timespec ts;

    /*
     * Use the same clock that was configured in tl_cond_init().
     * The condvar and timeout calculation MUST use the same clock,
     * otherwise timeouts will be wrong (possibly very long or immediate).
     */
#if TL_HAS_PTHREAD_CONDATTR_SETCLOCK
    if (cv->use_monotonic) {
        clock_gettime(CLOCK_MONOTONIC, &ts);
    } else {
        clock_gettime(CLOCK_REALTIME, &ts);
    }
#else
    /* CLOCK_MONOTONIC not available for condvars, use REALTIME */
    clock_gettime(CLOCK_REALTIME, &ts);
#endif

    /* Add timeout */
    ts.tv_sec += timeout_ms / 1000;
    ts.tv_nsec += (timeout_ms % 1000) * 1000000L;
    /* Handle nanosecond overflow */
    if (ts.tv_nsec >= 1000000000L) {
        ts.tv_sec += 1;
        ts.tv_nsec -= 1000000000L;
    }

#ifdef TL_DEBUG
    TL_ASSERT(mu->locked);
    /* Mark as unlocked before wait */
    mu->locked = 0;
#endif
    int rc = pthread_cond_timedwait(&cv->cond, &mu->lock, &ts);
#ifdef TL_DEBUG
    /* Mutex is reacquired after wait */
    mu->owner = pthread_self();
    mu->locked = 1;
#endif

    if (rc == 0) {
        return true;  /* Signaled */
    }
    if (rc == ETIMEDOUT) {
        return false; /* Timed out */
    }
    TL_ASSERT(0); /* Unexpected error */
    return false;
}

void tl_cond_signal(tl_cond_t* cv) {
    TL_ASSERT(cv != NULL);
    pthread_cond_signal(&cv->cond);
}

void tl_cond_broadcast(tl_cond_t* cv) {
    TL_ASSERT(cv != NULL);
    pthread_cond_broadcast(&cv->cond);
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

uint64_t tl_thread_self_id(void) {
    /*
     * pthread_t is an opaque type that may not be integer-convertible.
     * We use memcpy to safely extract a numeric ID for debugging purposes.
     * This ID is only used for debug output and lock tracking, not for
     * thread comparison (use pthread_equal() for that).
     */
    pthread_t self = pthread_self();
    uint64_t id = 0;
    size_t copy_size = sizeof(self) < sizeof(id) ? sizeof(self) : sizeof(id);
    memcpy(&id, &self, copy_size);
    return id;
}

#ifdef TL_DEBUG
void tl_thread_set_name(const char* name) {
    if (name == NULL) return;

#if defined(__APPLE__)
    /* macOS: pthread_setname_np takes only the name (current thread implicit) */
    pthread_setname_np(name);
#elif defined(__linux__)
    /* Linux: pthread_setname_np takes thread handle and name (max 15 chars + NUL) */
    pthread_setname_np(pthread_self(), name);
#else
    /* Other POSIX: best-effort no-op */
    (void)name;
#endif
}
#endif

void tl_thread_yield(void) {
    sched_yield();
}

void tl_sleep_ms(uint32_t ms) {
    /*
     * Use nanosleep instead of usleep:
     * - usleep is obsolete in POSIX.1-2008
     * - nanosleep handles interrupts properly (EINTR)
     * - nanosleep provides remaining time on interrupt
     */
    struct timespec ts;
    ts.tv_sec = ms / 1000;
    ts.tv_nsec = (ms % 1000) * 1000000L;

    while (nanosleep(&ts, &ts) == -1 && errno == EINTR) {
        /* Retry with remaining time if interrupted */
    }
}

uint64_t tl_monotonic_ms(void) {
    struct timespec ts;
#if defined(CLOCK_MONOTONIC)
    clock_gettime(CLOCK_MONOTONIC, &ts);
#else
    /* Fallback to realtime if monotonic unavailable (rare) */
    clock_gettime(CLOCK_REALTIME, &ts);
#endif
    return (uint64_t)ts.tv_sec * 1000 + (uint64_t)ts.tv_nsec / 1000000;
}

#endif /* Platform selection */
