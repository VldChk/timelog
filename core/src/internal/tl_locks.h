#ifndef TL_LOCKS_H
#define TL_LOCKS_H

#include "tl_sync.h"

/*===========================================================================
 * Lock Ordering (from timelog_v1_engineering_plan.md)
 *
 * Strict order: maint_mu -> flush_mu -> writer_mu -> memtable_mu
 *
 * Rules:
 * - Never acquire a lock while holding one to its right
 * - Long builds happen off-lock (only short critical sections under writer_mu)
 * - Deferred signaling: set flag, then signal under maint_mu
 *===========================================================================*/

typedef enum tl_lock_id {
    TL_LOCK_NONE       = 0,
    TL_LOCK_MAINT_MU   = 1,  /* Highest priority */
    TL_LOCK_FLUSH_MU   = 2,
    TL_LOCK_WRITER_MU  = 3,
    TL_LOCK_MEMTABLE_MU = 4  /* Lowest priority */
} tl_lock_id_t;

#ifdef TL_DEBUG

/*===========================================================================
 * Debug-Mode Lock Tracking
 *
 * Each thread maintains a stack of held locks to detect ordering violations.
 * This uses thread-local storage for per-thread tracking.
 *===========================================================================*/

#define TL_MAX_HELD_LOCKS 8

typedef struct tl_lock_tracker {
    tl_lock_id_t held[TL_MAX_HELD_LOCKS];
    int depth;
} tl_lock_tracker_t;

/* Thread-local lock tracker */
#if defined(TL_PLATFORM_WINDOWS)
    extern __declspec(thread) tl_lock_tracker_t tl__lock_tracker;
#else
    extern __thread tl_lock_tracker_t tl__lock_tracker;
#endif

/**
 * Record that a lock is being acquired.
 * Asserts if acquiring out of order.
 */
TL_INLINE void tl_lock_acquire_check(tl_lock_id_t id) {
    tl_lock_tracker_t* t = &tl__lock_tracker;

    /* Check ordering: new lock must be > all held locks */
    for (int i = 0; i < t->depth; i++) {
        TL_ASSERT_MSG(t->held[i] < id,
            "Lock ordering violation: cannot acquire lower-priority lock");
    }

    TL_ASSERT(t->depth < TL_MAX_HELD_LOCKS);
    t->held[t->depth++] = id;
}

/**
 * Record that a lock is being released.
 * Asserts if releasing out of order.
 */
TL_INLINE void tl_lock_release_check(tl_lock_id_t id) {
    tl_lock_tracker_t* t = &tl__lock_tracker;

    TL_ASSERT(t->depth > 0);
    TL_ASSERT_MSG(t->held[t->depth - 1] == id,
        "Lock release order violation: must release in reverse order");
    t->depth--;
}

/**
 * Check if a specific lock is held.
 */
TL_INLINE bool tl_lock_is_held(tl_lock_id_t id) {
    const tl_lock_tracker_t* t = &tl__lock_tracker;
    for (int i = 0; i < t->depth; i++) {
        if (t->held[i] == id) return true;
    }
    return false;
}

/**
 * Get the highest-priority lock currently held.
 */
TL_INLINE tl_lock_id_t tl_lock_highest_held(void) {
    tl_lock_tracker_t* t = &tl__lock_tracker;
    if (t->depth == 0) return TL_LOCK_NONE;
    return t->held[0]; /* First acquired = highest priority */
}

/* Macros for lock operations with tracking */
#define TL_LOCK(mu, id) do { \
    tl_lock_acquire_check(id); \
    tl_mutex_lock(mu); \
} while(0)

#define TL_UNLOCK(mu, id) do { \
    tl_mutex_unlock(mu); \
    tl_lock_release_check(id); \
} while(0)

#define TL_TRYLOCK(mu, id, result) do { \
    tl_lock_acquire_check(id); \
    (result) = tl_mutex_trylock(mu); \
    if (!(result)) { \
        tl_lock_release_check(id); \
    } \
} while(0)

#else /* !TL_DEBUG */

/* Release mode: no tracking overhead */
#define TL_LOCK(mu, id)           tl_mutex_lock(mu)
#define TL_UNLOCK(mu, id)         tl_mutex_unlock(mu)
#define TL_TRYLOCK(mu, id, result) ((result) = tl_mutex_trylock(mu))

#define tl_lock_acquire_check(id) ((void)0)
#define tl_lock_release_check(id) ((void)0)
#define tl_lock_is_held(id)       (false)
#define tl_lock_highest_held()    (TL_LOCK_NONE)

#endif /* TL_DEBUG */

/*===========================================================================
 * Named Lock Macros for Clarity
 *===========================================================================*/

/* Writer mutex - serializes manifest publication */
#define TL_LOCK_WRITER(tl)    TL_LOCK(&(tl)->writer_mu, TL_LOCK_WRITER_MU)
#define TL_UNLOCK_WRITER(tl)  TL_UNLOCK(&(tl)->writer_mu, TL_LOCK_WRITER_MU)

/* Flush mutex - single flusher at a time */
#define TL_LOCK_FLUSH(tl)     TL_LOCK(&(tl)->flush_mu, TL_LOCK_FLUSH_MU)
#define TL_UNLOCK_FLUSH(tl)   TL_UNLOCK(&(tl)->flush_mu, TL_LOCK_FLUSH_MU)

/* Maintenance mutex - protects maint state */
#define TL_LOCK_MAINT(tl)     TL_LOCK(&(tl)->maint_mu, TL_LOCK_MAINT_MU)
#define TL_UNLOCK_MAINT(tl)   TL_UNLOCK(&(tl)->maint_mu, TL_LOCK_MAINT_MU)

/* Memtable mutex - protects sealed queue */
#define TL_LOCK_MEMTABLE(tl)   TL_LOCK(&(tl)->memtable_mu, TL_LOCK_MEMTABLE_MU)
#define TL_UNLOCK_MEMTABLE(tl) TL_UNLOCK(&(tl)->memtable_mu, TL_LOCK_MEMTABLE_MU)

#endif /* TL_LOCKS_H */
