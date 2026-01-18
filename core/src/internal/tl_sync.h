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
 * Design: Use SRWLock on Windows (fast, slim) and pthread_mutex on POSIX.
 * Both are non-recursive by default, which matches our usage.
 *===========================================================================*/

#if defined(TL_PLATFORM_WINDOWS)

typedef struct tl_mutex {
    SRWLOCK lock;
#ifdef TL_DEBUG
    volatile DWORD owner;  /* Thread ID of owner, 0 if unlocked */
#endif
} tl_mutex_t;

#else /* POSIX */

typedef struct tl_mutex {
    pthread_mutex_t lock;
#ifdef TL_DEBUG
    /*
     * IMPORTANT: pthread_t is an opaque type - we cannot assign 0 to it.
     * We use 'locked' as the primary indicator and only read 'owner' when
     * 'locked' is true. The owner field is only valid when locked == 1.
     */
    pthread_t owner;    /* Valid only when locked == 1 */
    int locked;         /* 0 = unlocked, 1 = locked */
#endif
} tl_mutex_t;

#endif

/**
 * Initialize a mutex.
 * @return TL_OK on success, TL_EINTERNAL on failure
 */
tl_status_t tl_mutex_init(tl_mutex_t* mu);

/**
 * Destroy a mutex.
 * Mutex must be unlocked. Behavior undefined if locked.
 */
void tl_mutex_destroy(tl_mutex_t* mu);

/**
 * Acquire mutex (blocking).
 */
void tl_mutex_lock(tl_mutex_t* mu);

/**
 * Release mutex.
 * Must be called by the thread that locked it.
 */
void tl_mutex_unlock(tl_mutex_t* mu);

/**
 * Try to acquire mutex (non-blocking).
 * @return true if acquired, false if already locked
 */
bool tl_mutex_trylock(tl_mutex_t* mu);

#ifdef TL_DEBUG
/**
 * Check if current thread holds the mutex (debug only).
 */
bool tl_mutex_is_held(const tl_mutex_t* mu);
#endif

/*===========================================================================
 * Condition Variable
 *
 * Design: Use CONDITION_VARIABLE on Windows, pthread_cond on POSIX.
 *===========================================================================*/

#if defined(TL_PLATFORM_WINDOWS)

typedef struct tl_cond {
    CONDITION_VARIABLE cond;
} tl_cond_t;

#else /* POSIX */

typedef struct tl_cond {
    pthread_cond_t cond;
    bool use_monotonic;  /* true if using CLOCK_MONOTONIC, false for CLOCK_REALTIME */
} tl_cond_t;

#endif

/**
 * Initialize a condition variable.
 * @return TL_OK on success, TL_EINTERNAL on failure
 */
tl_status_t tl_cond_init(tl_cond_t* cv);

/**
 * Destroy a condition variable.
 */
void tl_cond_destroy(tl_cond_t* cv);

/**
 * Wait on condition variable.
 * Mutex must be held; it is released during wait and reacquired before return.
 */
void tl_cond_wait(tl_cond_t* cv, tl_mutex_t* mu);

/**
 * Wait on condition variable with timeout.
 * @param timeout_ms Maximum wait time in milliseconds
 * @return true if signaled, false if timed out
 */
bool tl_cond_timedwait(tl_cond_t* cv, tl_mutex_t* mu, uint32_t timeout_ms);

/**
 * Signal one waiting thread.
 */
void tl_cond_signal(tl_cond_t* cv);

/**
 * Signal all waiting threads.
 */
void tl_cond_broadcast(tl_cond_t* cv);

/*===========================================================================
 * Thread
 *
 * Design: Simple wrapper for background maintenance thread.
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

/**
 * Create and start a new thread.
 * @param thread Output thread handle
 * @param fn Thread function
 * @param arg Argument passed to fn
 * @return TL_OK on success, TL_EINTERNAL on failure
 */
tl_status_t tl_thread_create(tl_thread_t* thread, tl_thread_fn fn, void* arg);

/**
 * Wait for thread to complete and retrieve result.
 * @param thread Thread to join
 * @param result Optional output for thread return value
 * @return TL_OK on success
 */
tl_status_t tl_thread_join(tl_thread_t* thread, void** result);

/**
 * Get current thread ID (for debugging).
 */
uint64_t tl_thread_self_id(void);

#ifdef TL_DEBUG
/**
 * Set name for the current thread (debug only, for profilers/debuggers).
 *
 * Thread names appear in debuggers, profilers, and tools like htop.
 * This is useful for identifying maintenance worker threads.
 *
 * Platform support:
 * - Windows: SetThreadDescription (Windows 10 1607+, silently fails on older)
 * - Linux: pthread_setname_np (truncates to 15 chars)
 * - macOS: pthread_setname_np (truncates to 63 chars)
 *
 * @param name Thread name (null-terminated, may be truncated by platform)
 */
void tl_thread_set_name(const char* name);
#endif

/*===========================================================================
 * Yield and Sleep
 *===========================================================================*/

/**
 * Yield to other threads.
 */
void tl_thread_yield(void);

/**
 * Sleep for specified milliseconds.
 */
void tl_sleep_ms(uint32_t ms);

/*===========================================================================
 * Monotonic Time
 *===========================================================================*/

/**
 * Get current monotonic time in milliseconds.
 * Used for computing elapsed time in bounded waits.
 * The absolute value is meaningless; only differences are useful.
 */
uint64_t tl_monotonic_ms(void);

#endif /* TL_SYNC_H */
