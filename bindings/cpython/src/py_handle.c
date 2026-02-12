/**
 * @file py_handle.c
 * @brief Python handle and lifetime management subsystem implementation
 *
 * Implements the LLD-B1 specification for storing CPython objects as
 * tl_handle_t values with correct lifetime management.
 *
 * Key design decisions:
 * - Lock-free Treiber stack for retired object queue (MPSC pattern)
 * - Pin counter prevents drain while snapshots are active
 * - on_drop callback does NOT acquire GIL or call Python C-API
 * - All Py_DECREF happens in drain() on Python threads with GIL held
 *
 * Memory ordering model:
 * - Pin increment: RELAXED (gating counter, not a publication barrier;
 *   actual sync happens via Timelog snapshot acquisition)
 * - Pin decrement: RELEASE (ensures iterator operations visible to drain)
 * - Stack push CAS: RELEASE (make node fields visible)
 * - Stack exchange (drain): ACQ_REL (see all pushed nodes)
 *
 * See: docs/V2/timelog_v2_engineering_plan.md
 *      docs/V2/timelog_v2_c_software_design_spec.md
 */

#include "timelogpy/py_handle.h"

#include <assert.h>   /* assert for debug checks */
#include <inttypes.h> /* PRIu64 for portable uint64_t formatting */
#include <stdio.h>    /* fprintf, stderr */
#include <stdlib.h>   /* malloc, free - NOT Python allocators (no GIL in on_drop) */
#include <string.h>   /* memset */

/*===========================================================================
 * Live Handle Tracking (multiset)
 *===========================================================================*/

/* Hash table entry states */
#define TL_PY_LIVE_EMPTY     0
#define TL_PY_LIVE_FULL      1
#define TL_PY_LIVE_TOMBSTONE 2

struct tl_py_live_entry {
    PyObject* obj;
    uint64_t  count;
    uint8_t   state;
};

static size_t tl_py_live_hash_ptr(const void* ptr)
{
    uintptr_t x = (uintptr_t)ptr;
    /* Simple mix; sufficient for pointer keys */
    x ^= x >> 17;
    x *= (uintptr_t)0xed5ad4bbU;
    x ^= x >> 11;
    x *= (uintptr_t)0xac4c1b51U;
    x ^= x >> 15;
    return (size_t)x;
}

static tl_status_t tl_py_live_rehash(tl_py_handle_ctx_t* ctx, size_t new_cap)
{
    tl_py_live_entry_t* old_entries = ctx->live_entries;
    size_t old_cap = ctx->live_cap;

    tl_py_live_entry_t* entries = (tl_py_live_entry_t*)calloc(
        new_cap, sizeof(*entries));
    if (entries == NULL) {
        return TL_ENOMEM;
    }

    ctx->live_entries = entries;
    ctx->live_cap = new_cap;
    ctx->live_len = 0;
    ctx->live_tombstones = 0;

    if (old_entries != NULL) {
        for (size_t i = 0; i < old_cap; i++) {
            if (old_entries[i].state == TL_PY_LIVE_FULL) {
                /* Reinsert */
                PyObject* obj = old_entries[i].obj;
                uint64_t count = old_entries[i].count;
                size_t mask = ctx->live_cap - 1;
                size_t idx = tl_py_live_hash_ptr(obj) & mask;
                for (;;) {
                    tl_py_live_entry_t* e = &ctx->live_entries[idx];
                    if (e->state == TL_PY_LIVE_EMPTY) {
                        e->state = TL_PY_LIVE_FULL;
                        e->obj = obj;
                        e->count = count;
                        ctx->live_len++;
                        break;
                    }
                    idx = (idx + 1) & mask;
                }
            }
        }
        free(old_entries);
    }

    return TL_OK;
}

static tl_status_t tl_py_live_ensure(tl_py_handle_ctx_t* ctx, size_t needed)
{
    size_t cap = ctx->live_cap;
    if (cap == 0) {
        size_t init_cap = 64;
        if (init_cap < needed) {
            while (init_cap < needed) {
                init_cap *= 2;
            }
        }
        return tl_py_live_rehash(ctx, init_cap);
    }

    /* Keep load factor <= ~0.7 (including tombstones) */
    size_t used = ctx->live_len + ctx->live_tombstones + needed;
    if (used * 10 <= cap * 7) {
        return TL_OK;
    }

    size_t new_cap = cap * 2;
    if (new_cap < cap) {
        return TL_EOVERFLOW;
    }
    return tl_py_live_rehash(ctx, new_cap);
}
/*===========================================================================
 * Compile-Time Validation
 *===========================================================================*/

/**
 * Verify that we have proper C11/C17 atomics.
 * The Python.h include already requires a modern compiler, so this should
 * always succeed. If not, we need to add MSVC intrinsics fallback.
 */
#if !defined(__STDC_VERSION__) || __STDC_VERSION__ < 201112L
    #error "C11 or later required for stdatomic.h"
#endif

#if defined(__STDC_NO_ATOMICS__)
    #error "Compiler does not support C11 atomics"
#endif

/*===========================================================================
 * Lifecycle Implementation
 *===========================================================================*/

tl_status_t tl_py_handle_ctx_init(tl_py_handle_ctx_t* ctx,
                                   uint32_t drain_batch_limit)
{
    if (ctx == NULL) {
        return TL_EINVAL;
    }

    /* Initialize atomics */
    atomic_init(&ctx->retired_head, NULL);
    atomic_init(&ctx->pins, 0);
    atomic_init(&ctx->retired_count, 0);
    atomic_init(&ctx->drained_count, 0);
    atomic_init(&ctx->alloc_failures, 0);
    atomic_flag_clear_explicit(&ctx->drain_guard, memory_order_release);

    /* Store configuration (immutable after init) */
    ctx->drain_batch_limit = drain_batch_limit;
    ctx->live_entries = NULL;
    ctx->live_cap = 0;
    ctx->live_len = 0;
    ctx->live_tombstones = 0;
    ctx->live_tracking_failed = 0;

    return TL_OK;
}

void tl_py_handle_ctx_destroy(tl_py_handle_ctx_t* ctx)
{
    if (ctx == NULL) {
        return;
    }

    /*
     * Caller should have drained the queue before destruction.
     * If not, we have a leak but cannot safely DECREF without GIL.
     * Log a warning in debug builds.
     */
#ifndef NDEBUG
    tl_py_drop_node_t* remaining = atomic_load_explicit(
        &ctx->retired_head, memory_order_relaxed);
    if (remaining != NULL) {
        fprintf(stderr,
            "WARNING: tl_py_handle_ctx_destroy called with non-empty queue. "
            "Objects will leak.\n");
    }

    uint64_t pins = atomic_load_explicit(&ctx->pins, memory_order_relaxed);
    if (pins != 0) {
        fprintf(stderr,
            "WARNING: tl_py_handle_ctx_destroy called with pins=%" PRIu64 ". "
            "This indicates a snapshot/iterator leak.\n",
            pins);
    }

    if (ctx->live_len != 0) {
        fprintf(stderr,
            "WARNING: tl_py_handle_ctx_destroy called with %zu live objects. "
            "Did you forget to call tl_py_live_release_all()?\n",
            ctx->live_len);
    }
#endif

    if (ctx->live_entries != NULL) {
        free(ctx->live_entries);
    }

    ctx->live_entries = NULL;
    ctx->live_cap = 0;
    ctx->live_len = 0;
    ctx->live_tombstones = 0;
    ctx->live_tracking_failed = 0;
}

/*===========================================================================
 * Pin Tracking Implementation (Invariant I3)
 *
 * Memory ordering rationale:
 * - RELAXED on increment: gating counter only; Timelog snapshot provides sync
 * - RELEASE on decrement: ensures drain sees all our iterator operations
 *
 * GIL requirement:
 * - pins_exit_and_maybe_drain must be called with GIL held (may call drain)
 *===========================================================================*/

void tl_py_pins_enter(tl_py_handle_ctx_t* ctx)
{
    /*
     * Memory ordering: RELAXED is sufficient here.
     *
     * The critical synchronization point is tl_snapshot_acquire() which
     * has its own memory barriers. The pin increment just needs to be
     * visible before any subsequent drain checks.
     *
     * See LLD-B1 Section 7.2: "increment pins **before** acquiring a
     * Timelog snapshot" - the protocol, not the ordering, provides safety.
     */
    atomic_fetch_add_explicit(&ctx->pins, 1, memory_order_relaxed);
}

void tl_py_pins_exit_and_maybe_drain(tl_py_handle_ctx_t* ctx)
{
#ifndef NDEBUG
    /*
     * GIL enforcement: drain may run, which calls Py_DECREF.
     * PyGILState_Check() returns 1 if current thread holds the GIL.
     */
    assert(PyGILState_Check() &&
           "tl_py_pins_exit_and_maybe_drain requires GIL");
#endif

    uint64_t old_pins = atomic_fetch_sub_explicit(
        &ctx->pins, 1, memory_order_release);

#ifndef NDEBUG
    /*
     * Pin underflow detection: if old_pins was 0, we wrapped to UINT64_MAX.
     * This indicates a misuse (exit without enter) and will deadlock drain.
     */
    assert(old_pins > 0 &&
           "Pin underflow: tl_py_pins_exit called without matching enter");
#endif

    /*
     * If we were the last pin holder (old_pins == 1 means new pins == 0),
     * opportunistically drain retired objects.
     */
    if (old_pins == 1) {
        (void)tl_py_drain_retired(ctx, 0);
    }
}

uint64_t tl_py_pins_count(const tl_py_handle_ctx_t* ctx)
{
    /*
     * Cast away const for atomic_load_explicit.
     * This is safe because atomic load doesn't modify semantic state.
     * The const qualifier on ctx is for API clarity, not memory safety.
     */
    return atomic_load_explicit(
        (_Atomic(uint64_t)*)&ctx->pins,
        memory_order_relaxed);
}

/*===========================================================================
 * On-Drop Callback Implementation (Invariant I4)
 *
 * CRITICAL CONSTRAINTS:
 * - Called from any thread invoking flush or compaction (NOT necessarily a Python thread)
 * - Does NOT hold the GIL
 * - Must NOT call any Python C-API functions
 * - Must NOT call back into Timelog APIs
 * - Must NOT block for extended periods
 *
 * Note: This is NOT async-signal-safe (uses malloc). It is only safe to
 * call from Timelog's flush or maintenance thread context.
 *
 * Implementation uses Treiber stack (lock-free LIFO):
 * 1. Allocate node with libc malloc (NOT Python allocator)
 * 2. Initialize node fields
 * 3. CAS loop to push onto stack head
 *===========================================================================*/

void tl_py_on_drop_handle(void* on_drop_ctx, tl_ts_t ts, tl_handle_t handle)
{
    if (on_drop_ctx == NULL) {
        /* Misconfiguration: callback registered without context. Silent fail. */
        return;
    }

    tl_py_handle_ctx_t* ctx = (tl_py_handle_ctx_t*)on_drop_ctx;

    /*
     * Allocate node with libc malloc.
     * We cannot use Python allocators here because:
     * 1. We don't hold the GIL
     * 2. Python allocator state may not be thread-safe without GIL
     */
    tl_py_drop_node_t* node = (tl_py_drop_node_t*)malloc(sizeof(*node));
    if (node == NULL) {
        /*
         * Allocation failure: increment counter and leak the object.
         * This is unfortunate but necessary to avoid use-after-free.
         * The object will never be DECREF'd, causing a memory leak.
         *
         * Policy rationale: leaking is safer than UAF. If we cannot
         * enqueue the drop, we cannot safely DECREF (no GIL), and we
         * cannot defer DECREF because we have nowhere to record it.
         */
        atomic_fetch_add_explicit(&ctx->alloc_failures, 1, memory_order_relaxed);
        return;
    }

    /* Initialize node fields BEFORE making visible via CAS */
    node->obj = tl_py_handle_decode(handle);
    node->ts = ts;

    /*
     * Treiber stack push (lock-free)
     *
     * Memory ordering:
     * - RELAXED load of head: no ordering needed, just reading current value
     * - RELEASE CAS: makes node fields visible to drain thread
     * - RELAXED failure: will retry with updated expected value
     *
     * Using weak CAS is fine since we're in a loop anyway.
     */
    tl_py_drop_node_t* head;
    do {
        head = atomic_load_explicit(&ctx->retired_head, memory_order_relaxed);
        node->next = head;
    } while (!atomic_compare_exchange_weak_explicit(
                &ctx->retired_head,
                &head,
                node,
                memory_order_release,
                memory_order_relaxed));

    /* Update metrics (relaxed is fine for counters) */
    atomic_fetch_add_explicit(&ctx->retired_count, 1, memory_order_relaxed);
}

/*===========================================================================
 * Drain Implementation
 *
 * PRECONDITION: Caller must hold the GIL.
 *
 * This function performs the actual Py_DECREF operations for retired
 * objects. It runs on a Python thread to ensure:
 * 1. Finalizers (__del__) run on a proper Python thread
 * 2. No GIL acquisition needed (already held)
 * 3. Proper integration with Python's GC
 *===========================================================================*/

size_t tl_py_drain_retired(tl_py_handle_ctx_t* ctx, int force)
{
#ifndef NDEBUG
    /*
     * GIL enforcement: Py_DECREF can run arbitrary Python code via __del__.
     * This MUST be called from a Python thread holding the GIL.
     */
    assert(PyGILState_Check() &&
           "tl_py_drain_retired requires GIL");
#endif

    /*
     * Reentrancy guard: prevent nested drains triggered via __del__.
     * If already draining, bail out immediately.
     */
    if (atomic_flag_test_and_set_explicit(
            &ctx->drain_guard, memory_order_acquire)) {
        return 0;
    }

    size_t count = 0;

    /*
     * Check pin count before draining.
     *
     * If pins > 0, snapshots/iterators are active and might still yield
     * objects from the retired queue. Draining would cause use-after-free.
     *
     * Exception: force=1 is used during close() after verifying all
     * iterators are released.
     */
    uint64_t pins = atomic_load_explicit(&ctx->pins, memory_order_acquire);
    if (pins != 0 && !force) {
        goto out;
    }

    /*
     * Atomically claim the entire retired list.
     *
     * Memory ordering:
     * - ACQ_REL: acquire semantics to see node fields written by on_drop,
     *            release semantics to make our NULL write visible
     *
     * This makes the queue empty for subsequent on_drop calls.
     * We process the claimed list exclusively.
     */
    tl_py_drop_node_t* list = atomic_exchange_explicit(
        &ctx->retired_head, NULL, memory_order_acq_rel);

    if (list == NULL) {
        goto out;  /* Nothing to drain */
    }

    tl_py_drop_node_t* list_tail = list;
    while (list_tail->next != NULL) {
        list_tail = list_tail->next;
    }

    /*
     * Batch limit: 0 = unlimited.
     * When force=1 (close path), always drain everything regardless of limit.
     * This prevents leaking objects when ctx is about to be destroyed.
     */
    uint32_t batch_limit = force ? 0 : ctx->drain_batch_limit;

    while (list != NULL) {
        /* Check batch limit (0 = unlimited) */
        if (batch_limit != 0 && count >= batch_limit) {
            /*
             * Batch limit reached. Re-attach remaining nodes to queue.
             * Must be done atomically in case on_drop is concurrent.
             */
            tl_py_drop_node_t* remaining = list;

            /* Atomically prepend remaining to current queue head */
            tl_py_drop_node_t* current_head;
            do {
                current_head = atomic_load_explicit(
                    &ctx->retired_head, memory_order_relaxed);
                list_tail->next = current_head;
            } while (!atomic_compare_exchange_weak_explicit(
                        &ctx->retired_head,
                        &current_head,
                        remaining,
                        memory_order_release,
                        memory_order_relaxed));
            break;
        }

        /* Process one node */
        tl_py_drop_node_t* node = list;
        list = node->next;
        if (list == NULL) {
            list_tail = NULL;
        }

        /* Update live tracking before DECREF */
        tl_py_live_note_drop(ctx, node->obj);

        /*
         * CRITICAL: Py_DECREF may run arbitrary Python code via __del__.
         *
         * This is safe because:
         * 1. We hold the GIL (precondition)
         * 2. We're on a Python thread
         * 3. The object is no longer reachable from Timelog
         * 4. pins == 0 (no iterator can yield this object)
         */
        Py_DECREF(node->obj);

        /* Free the node (allocated with libc malloc) */
        free(node);
        count++;
    }

    /* Update metrics */
    atomic_fetch_add_explicit(&ctx->drained_count, count, memory_order_relaxed);

out:
    atomic_flag_clear_explicit(&ctx->drain_guard, memory_order_release);
    return count;
}

/*===========================================================================
 * Live Handle Tracking (multiset) Implementation
 *===========================================================================*/

tl_status_t tl_py_live_note_insert(tl_py_handle_ctx_t* ctx, PyObject* obj)
{
#ifndef NDEBUG
    assert(PyGILState_Check() &&
           "tl_py_live_note_insert requires GIL");
#endif

    if (ctx == NULL || obj == NULL) {
        return TL_EINVAL;
    }

    tl_status_t st = tl_py_live_ensure(ctx, 1);
    if (st != TL_OK) {
        ctx->live_tracking_failed = 1;
        return st;
    }

    size_t mask = ctx->live_cap - 1;
    size_t idx = tl_py_live_hash_ptr(obj) & mask;
    size_t first_tombstone = (size_t)-1;

    for (;;) {
        tl_py_live_entry_t* e = &ctx->live_entries[idx];
        if (e->state == TL_PY_LIVE_EMPTY) {
            if (first_tombstone != (size_t)-1) {
                e = &ctx->live_entries[first_tombstone];
                ctx->live_tombstones--;
            }
            e->state = TL_PY_LIVE_FULL;
            e->obj = obj;
            e->count = 1;
            ctx->live_len++;
            return TL_OK;
        }
        if (e->state == TL_PY_LIVE_TOMBSTONE) {
            if (first_tombstone == (size_t)-1) {
                first_tombstone = idx;
            }
        } else if (e->obj == obj) {
            e->count++;
            return TL_OK;
        }
        idx = (idx + 1) & mask;
    }
}

void tl_py_live_note_drop(tl_py_handle_ctx_t* ctx, PyObject* obj)
{
#ifndef NDEBUG
    assert(PyGILState_Check() &&
           "tl_py_live_note_drop requires GIL");
#endif

    if (ctx == NULL || obj == NULL || ctx->live_cap == 0) {
        return;
    }

    size_t mask = ctx->live_cap - 1;
    size_t idx = tl_py_live_hash_ptr(obj) & mask;

    for (;;) {
        tl_py_live_entry_t* e = &ctx->live_entries[idx];
        if (e->state == TL_PY_LIVE_EMPTY) {
            return;
        }
        if (e->state == TL_PY_LIVE_FULL && e->obj == obj) {
            if (e->count > 1) {
                e->count--;
                return;
            }
            e->obj = NULL;
            e->count = 0;
            e->state = TL_PY_LIVE_TOMBSTONE;
            ctx->live_len--;
            ctx->live_tombstones++;
            return;
        }
        idx = (idx + 1) & mask;
    }
}

void tl_py_live_release_all(tl_py_handle_ctx_t* ctx)
{
#ifndef NDEBUG
    assert(PyGILState_Check() &&
           "tl_py_live_release_all requires GIL");
#endif

    if (ctx == NULL || ctx->live_entries == NULL) {
        return;
    }

#ifndef NDEBUG
    if (ctx->live_tracking_failed) {
        fprintf(stderr,
            "WARNING: live handle tracking encountered allocation failures; "
            "some objects may leak.\n");
    }
#endif

    for (size_t i = 0; i < ctx->live_cap; i++) {
        tl_py_live_entry_t* e = &ctx->live_entries[i];
        if (e->state == TL_PY_LIVE_FULL) {
            for (uint64_t c = e->count; c > 0; c--) {
                Py_DECREF(e->obj);
            }
            e->obj = NULL;
            e->count = 0;
            e->state = TL_PY_LIVE_EMPTY;
        }
    }

    free(ctx->live_entries);
    ctx->live_entries = NULL;
    ctx->live_cap = 0;
    ctx->live_len = 0;
    ctx->live_tombstones = 0;
}

int tl_py_handle_ctx_traverse(tl_py_handle_ctx_t* ctx, visitproc visit, void* arg)
{
#ifndef NDEBUG
    assert(PyGILState_Check() &&
           "tl_py_handle_ctx_traverse requires GIL");
#endif
    if (ctx == NULL || visit == NULL) {
        return 0;
    }

    if (ctx->live_entries != NULL) {
        for (size_t i = 0; i < ctx->live_cap; i++) {
            tl_py_live_entry_t* e = &ctx->live_entries[i];
            if (e->state == TL_PY_LIVE_FULL && e->obj != NULL) {
                int st = visit(e->obj, arg);
                if (st != 0) {
                    return st;
                }
            }
        }
    }

    tl_py_drop_node_t* retired = atomic_load_explicit(
        &ctx->retired_head, memory_order_acquire);
    while (retired != NULL) {
        if (retired->obj != NULL) {
            int st = visit(retired->obj, arg);
            if (st != 0) {
                return st;
            }
        }
        retired = retired->next;
    }

    return 0;
}

void tl_py_handle_ctx_clear(tl_py_handle_ctx_t* ctx)
{
#ifndef NDEBUG
    assert(PyGILState_Check() &&
           "tl_py_handle_ctx_clear requires GIL");
#endif
    if (ctx == NULL) {
        return;
    }
    (void)tl_py_drain_retired(ctx, 1);
    tl_py_live_release_all(ctx);
}

/*===========================================================================
 * Metrics Implementation
 *===========================================================================*/

uint64_t tl_py_retired_queue_len(const tl_py_handle_ctx_t* ctx)
{
    /*
     * Cast away const for atomic_load_explicit.
     * Note: drained_count is updated after re-attachment in batch mode,
     * so this metric may briefly undercount. This is documented as approximate.
     */
    uint64_t retired = atomic_load_explicit(
        (_Atomic(uint64_t)*)&ctx->retired_count,
        memory_order_relaxed);
    uint64_t drained = atomic_load_explicit(
        (_Atomic(uint64_t)*)&ctx->drained_count,
        memory_order_relaxed);

    /* Underflow protection (should never happen but defensive) */
    if (drained > retired) {
        return 0;
    }

    return retired - drained;
}

uint64_t tl_py_alloc_failures(const tl_py_handle_ctx_t* ctx)
{
    return atomic_load_explicit(
        (_Atomic(uint64_t)*)&ctx->alloc_failures,
        memory_order_relaxed);
}
