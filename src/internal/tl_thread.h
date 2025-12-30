#ifndef TL_THREAD_H
#define TL_THREAD_H

#include <stdbool.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Platform-specific includes and type definitions
 */
#if defined(_WIN32)
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>

typedef CRITICAL_SECTION tl_mutex_t;
typedef CONDITION_VARIABLE tl_cond_t;
typedef HANDLE tl_thread_t;

#else /* POSIX */
#include <pthread.h>

typedef pthread_mutex_t tl_mutex_t;
typedef pthread_cond_t tl_cond_t;
typedef pthread_t tl_thread_t;
#endif

/*
 * Thread function type.
 * Returns void* for POSIX compatibility.
 */
typedef void* (*tl_thread_fn)(void* arg);

/*
 * Mutex operations
 */
int  tl_mutex_init(tl_mutex_t* mtx);
void tl_mutex_destroy(tl_mutex_t* mtx);
void tl_mutex_lock(tl_mutex_t* mtx);
void tl_mutex_unlock(tl_mutex_t* mtx);
bool tl_mutex_trylock(tl_mutex_t* mtx);

/*
 * Condition variable operations
 */
int  tl_cond_init(tl_cond_t* cond);
void tl_cond_destroy(tl_cond_t* cond);
void tl_cond_signal(tl_cond_t* cond);
void tl_cond_broadcast(tl_cond_t* cond);
void tl_cond_wait(tl_cond_t* cond, tl_mutex_t* mtx);

/**
 * Timed wait (for bounded blocking)
 * @param timeout_ms Maximum milliseconds to wait
 * @return true if signaled, false if timeout
 */
bool tl_cond_timedwait(tl_cond_t* cond, tl_mutex_t* mtx, uint32_t timeout_ms);

/*
 * Thread operations
 */

/**
 * Create a new thread.
 *
 * @param thread  Output thread handle
 * @param fn      Thread function to execute
 * @param arg     Argument passed to thread function
 * @return 0 on success, non-zero on error
 */
int tl_thread_create(tl_thread_t* thread, tl_thread_fn fn, void* arg);

/**
 * Wait for a thread to terminate.
 *
 * @param thread  Thread handle
 * @param retval  Output for thread return value (may be NULL)
 * @return 0 on success, non-zero on error
 */
int tl_thread_join(tl_thread_t thread, void** retval);

#ifdef __cplusplus
}
#endif

#endif /* TL_THREAD_H */
