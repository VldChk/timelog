#ifndef TL_SYNC_H
#define TL_SYNC_H

#include "tl_defs.h"
#include "tl_atomic.h"

/*===========================================================================
 * Platform Includes
 *===========================================================================*/

#if defined(TL_PLATFORM_WINDOWS)
    #ifndef WIN32_LEAN_AND_MEAN
        #define WIN32_LEAN_AND_MEAN
    #endif
    #include <windows.h>
#else
    #include <pthread.h>
    #include <errno.h>
#endif

/*===========================================================================
 * Mutex
 *
 * Backed by SRWLock on Windows (slim, fast, non-recursive) and
 * pthread_mutex on POSIX. Both implementations are non-recursive by
 * design — the engine never re-enters a mutex it already holds.
 *===========================================================================*/

#if defined(TL_PLATFORM_WINDOWS)

typedef struct tl_mutex {
    SRWLOCK lock;
#ifdef TL_DEBUG
    volatile DWORD owner;  /* Thread ID of owner; 0 means unlocked. */
#endif
} tl_mutex_t;

#else /* POSIX */

typedef struct tl_mutex {
    pthread_mutex_t lock;
#ifdef TL_DEBUG
    /*
     * pthread_t is opaque, so we cannot use a sentinel value to mean
     * "unlocked". The companion 'locked' flag carries that information,
     * and owner is only meaningful while locked == 1.
     */
    pthread_t owner;
    int locked;
#endif
} tl_mutex_t;

#endif

/** @return TL_OK on success, TL_EINTERNAL on platform failure. */
tl_status_t tl_mutex_init(tl_mutex_t* mu);

/** Destroy an unlocked mutex. Destroying a held mutex is undefined behaviour. */
void tl_mutex_destroy(tl_mutex_t* mu);

void tl_mutex_lock(tl_mutex_t* mu);

/** Must be called by the same thread that called tl_mutex_lock(). */
void tl_mutex_unlock(tl_mutex_t* mu);

/** @return true if the mutex was acquired, false if already held. */
bool tl_mutex_trylock(tl_mutex_t* mu);

#ifdef TL_DEBUG
/** Debug-only ownership query, used to assert lock-order invariants. */
bool tl_mutex_is_held(const tl_mutex_t* mu);
#endif

/*===========================================================================
 * Condition Variable
 *
 * Backed by CONDITION_VARIABLE on Windows and pthread_cond on POSIX.
 *===========================================================================*/

#if defined(TL_PLATFORM_WINDOWS)

typedef struct tl_cond {
    CONDITION_VARIABLE cond;
} tl_cond_t;

#else /* POSIX */

typedef struct tl_cond {
    pthread_cond_t cond;
    /* Prefer CLOCK_MONOTONIC so timed waits are immune to wall-clock
     * jumps; fall back to CLOCK_REALTIME on platforms that don't support
     * setting the condvar clock attribute. */
    bool use_monotonic;
} tl_cond_t;

#endif

/** @return TL_OK on success, TL_EINTERNAL on platform failure. */
tl_status_t tl_cond_init(tl_cond_t* cv);

void tl_cond_destroy(tl_cond_t* cv);

/**
 * Wait on the condvar with the associated mutex held. The mutex is
 * released for the duration of the wait and re-acquired before return.
 */
void tl_cond_wait(tl_cond_t* cv, tl_mutex_t* mu);

/**
 * Bounded wait. @return true on a wake-up, false on timeout. Spurious
 * wake-ups are possible — callers must re-check their predicate.
 */
bool tl_cond_timedwait(tl_cond_t* cv, tl_mutex_t* mu, uint32_t timeout_ms);

void tl_cond_signal(tl_cond_t* cv);
void tl_cond_broadcast(tl_cond_t* cv);

/*===========================================================================
 * Thread
 *
 * Minimal wrapper around the platform thread API, used for the background
 * maintenance worker.
 *===========================================================================*/

typedef void* (*tl_thread_fn)(void* arg);

#if defined(TL_PLATFORM_WINDOWS)

typedef struct tl_thread {
    HANDLE handle;
    tl_thread_fn fn;
    void* arg;
    void* result;
} tl_thread_t;

#else /* POSIX */

typedef struct tl_thread {
    pthread_t handle;
    bool valid;
} tl_thread_t;

#endif

/** @return TL_OK on success, TL_EINTERNAL on platform failure. */
tl_status_t tl_thread_create(tl_thread_t* thread, tl_thread_fn fn, void* arg);

/** Block until the thread exits, optionally returning its result. */
tl_status_t tl_thread_join(tl_thread_t* thread, void** result);

/** Opaque identifier for the calling thread; debug/diagnostic use only. */
uint64_t tl_thread_self_id(void);

#ifdef TL_DEBUG
/**
 * Tag the current thread with a human-readable name so it shows up in
 * debuggers, profilers, and tools like htop. Each platform imposes its
 * own length limit and the name will be silently truncated to fit:
 * Linux pthread_setname_np caps at 15 chars, macOS at 63, Windows
 * (SetThreadDescription) requires Windows 10 1607 or newer and is a
 * no-op on older releases.
 */
void tl_thread_set_name(const char* name);
#endif

/*===========================================================================
 * Yield and Sleep
 *===========================================================================*/

void tl_thread_yield(void);

void tl_sleep_ms(uint32_t ms);

/*===========================================================================
 * Monotonic Time
 *===========================================================================*/

/**
 * Monotonic millisecond clock. The absolute value is implementation-
 * defined; only differences between two calls are meaningful. Used for
 * bounded-wait elapsed-time computations.
 */
uint64_t tl_monotonic_ms(void);

#endif /* TL_SYNC_H */
