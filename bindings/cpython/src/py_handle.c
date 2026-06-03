/**
 * @file py_handle.c
 * @brief Python handle and lifetime management subsystem implementation
 *
 * Implements the mechanism for storing CPython objects as
 * tl_handle_t values with correct lifetime management.
 *
 * Key design decisions:
 * - Lock-free Treiber stack for retired object queue (MPSC pattern)
 * - Pin counter prevents drain while snapshots are active
 * - on_drop callback does NOT acquire GIL or call Python C-API
 * - All Py_DECREF happens in drain() on the owning interpreter's attached
 *   Python thread state
 *
 * Memory ordering model:
 * - Pin increment: RELAXED while holding pin_lock (gating counter; actual
 *   snapshot data sync happens via Timelog snapshot acquisition)
 * - Pin decrement: RELEASE (ensures iterator operations visible to drain)
 * - Stack push CAS: ACQ_REL (make node fields visible and chain producers)
 * - Stack exchange (drain): ACQ_REL (see all pushed nodes)
 */

#include "timelogpy/py_handle.h"

#include <assert.h>   /* assert for debug checks */
#include <inttypes.h> /* PRIu64 for portable uint64_t formatting */
#include <stdio.h>    /* fprintf, stderr */
#include <stdlib.h>   /* malloc, free - NOT Python allocators in on_drop */
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

/*
 * Returns 1 if the current thread has an attached Python thread state that
 * belongs to the same interpreter that owns this ctx.
 *
 * Under free-threaded CPython the right precondition for Python C-API
 * access is "an attached thread state on the owning interpreter", not
 * "GIL held". On 3.13+ we query the thread state directly. On 3.12
 * (where free-threaded builds do not exist) the GIL-presence check is
 * equivalent.
 */
/*
 * The interpreter owning the currently-attached Python thread state, or NULL
 * if none is attached. On 3.13+ this asks the right free-threaded question
 * ("is a thread state attached?", via PyThreadState_GetUnchecked) rather than
 * "is the GIL held?" (PyGILState_Check), which does not track attachment under
 * Py_GIL_DISABLED. On 3.12 (no free-threaded build) the two are equivalent.
 * Used both to capture ctx->interp and to probe it, so the two never diverge.
 */
static PyInterpreterState* tl_py_current_interp_or_null(void)
{
    if (!Py_IsInitialized()) {
        return NULL;
    }
#if PY_VERSION_HEX >= 0x030D0000
    PyThreadState* ts = PyThreadState_GetUnchecked();
    return (ts != NULL) ? PyThreadState_GetInterpreter(ts) : NULL;
#else
    return PyGILState_Check() ? PyInterpreterState_Get() : NULL;
#endif
}

static int tl_py_attached_to_interp(const tl_py_handle_ctx_t* ctx)
{
    if (ctx == NULL) {
        return 0;
    }
    PyInterpreterState* cur = tl_py_current_interp_or_null();
    return cur != NULL && cur == ctx->interp;
}

static void tl_py_handle_ctx_warn_unsafe_destroy(const tl_py_handle_ctx_t* ctx,
                                                 const char* reason)
{
    tl_py_drop_node_t* remaining = atomic_load_explicit(
        (_Atomic(tl_py_drop_node_t*)*)&ctx->retired_head,
        memory_order_relaxed);
    uint64_t pins = atomic_load_explicit(
        (_Atomic(uint64_t)*)&ctx->pins, memory_order_relaxed);

    if (remaining != NULL || ctx->live_len != 0 || pins != 0) {
        fprintf(stderr,
            "WARNING: tl_py_handle_ctx final destroy skipped Python ref "
            "drain (%s): live=%zu retired=%p pins=%" PRIu64 ". "
            "Objects may leak.\n",
            reason,
            ctx->live_len,
            (void*)remaining,
            pins);
    }
}

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

/*
 * Push a [head..tail] sublist onto the lock-free retired stack (Treiber,
 * multi-producer). Used both by tl_py_on_drop_handle() (a single node, where
 * head==tail) and by the bounded-drain reattach path (an undrained suffix).
 *
 * The CAS is ACQ_REL, not plain RELEASE: the acquire half makes each producer
 * synchronize-with the producer that published the head it links behind, so
 * all live nodes form a single happens-before chain that the draining consumer
 * (an ACQ_REL exchange) joins. A release-only CAS would leave deeper nodes
 * reachable only via the C11 release-sequence-through-RMW rule, which C++20
 * weakened and which ThreadSanitizer does not model -- surfacing a
 * (benign-under-strict-C11 but fragile) malloc/free race on node memory.
 * Weak CAS is fine since we loop on failure.
 */
static void
tl_py_retired_push(tl_py_handle_ctx_t* ctx,
                   tl_py_drop_node_t* head,
                   tl_py_drop_node_t* tail)
{
    if (head == NULL) {
        return;
    }

    tl_py_drop_node_t* current_head;
    do {
        current_head = atomic_load_explicit(
            &ctx->retired_head, memory_order_acquire);
        tail->next = current_head;
    } while (!atomic_compare_exchange_weak_explicit(
                &ctx->retired_head,
                &current_head,
                head,
                memory_order_acq_rel,
                memory_order_acquire));
}

static size_t
tl_py_process_retired_list(tl_py_handle_ctx_t* ctx,
                           tl_py_drop_node_t* list,
                           int force)
{
    if (list == NULL) {
        return 0;
    }

    tl_py_drop_node_t* list_tail = list;
    while (list_tail->next != NULL) {
        list_tail = list_tail->next;
    }

    size_t count = 0;
    uint32_t batch_limit = force ? 0 : ctx->drain_batch_limit;

    while (list != NULL) {
        if (batch_limit != 0 && count >= batch_limit) {
            tl_py_retired_push(ctx, list, list_tail);
            break;
        }

        tl_py_drop_node_t* node = list;
        list = node->next;
        if (list == NULL) {
            list_tail = NULL;
        }

        tl_py_live_note_drop(ctx, node->obj);

        /* Safe: owning interpreter is attached, object unreachable from
         * Timelog, and this batch was claimed while pins were zero (or force
         * close explicitly overrode that check). */
        Py_DECREF(node->obj);

        free(node);
        count++;
    }

    if (count != 0) {
        atomic_fetch_add_explicit(&ctx->drained_count, count,
                                  memory_order_relaxed);
    }
    return count;
}

static tl_py_drop_node_t*
tl_py_claim_retired_for_drain_locked(tl_py_handle_ctx_t* ctx, int force)
{
    uint64_t pins = atomic_load_explicit(&ctx->pins, memory_order_acquire);
    if (pins != 0 && !force) {
        return NULL;
    }

    return atomic_exchange_explicit(
        &ctx->retired_head, NULL, memory_order_acq_rel);
}

static int
tl_py_try_begin_drain_and_claim_locked(tl_py_handle_ctx_t* ctx,
                                       int force,
                                       tl_py_drop_node_t** out)
{
    *out = NULL;
    if (atomic_flag_test_and_set_explicit(
            &ctx->drain_guard, memory_order_acquire)) {
        return 0;
    }
    *out = tl_py_claim_retired_for_drain_locked(ctx, force);
    return 1;
}

static void
tl_py_end_drain(tl_py_handle_ctx_t* ctx)
{
    atomic_flag_clear_explicit(&ctx->drain_guard, memory_order_release);
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
    atomic_init(&ctx->refcnt, 1);
    ctx->heap_allocated = 0;
    ctx->interp = tl_py_current_interp_or_null();
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
    atomic_init(&ctx->live_tracking_failed, 0);

    /* On 3.13+ PyMutex is statically zero-initializable and cannot fail;
     * on 3.12 the PyThread_type_lock fallback allocates and may return -1. */
    if (tl_py_mutex_init(&ctx->pin_lock) != 0) {
        return TL_ENOMEM;
    }
    if (tl_py_mutex_init(&ctx->live_lock) != 0) {
        tl_py_mutex_deinit(&ctx->pin_lock);
        return TL_ENOMEM;
    }

    return TL_OK;
}

tl_py_handle_ctx_t* tl_py_handle_ctx_new(uint32_t drain_batch_limit)
{
    tl_py_handle_ctx_t* ctx = PyMem_Malloc(sizeof(*ctx));
    if (ctx == NULL) {
        PyErr_NoMemory();
        return NULL;
    }

    if (tl_py_handle_ctx_init(ctx, drain_batch_limit) != TL_OK) {
        PyMem_Free(ctx);
        PyErr_NoMemory();
        return NULL;
    }

    ctx->heap_allocated = 1;
    return ctx;
}

void tl_py_handle_ctx_incref(tl_py_handle_ctx_t* ctx)
{
    if (ctx == NULL) {
        return;
    }
    atomic_fetch_add_explicit(&ctx->refcnt, 1, memory_order_relaxed);
}

void tl_py_handle_ctx_decref(tl_py_handle_ctx_t* ctx)
{
    if (ctx == NULL) {
        return;
    }

    uint64_t old_refcnt = atomic_fetch_sub_explicit(
        &ctx->refcnt, 1, memory_order_acq_rel);

#ifndef NDEBUG
    assert(old_refcnt > 0 && "handle context refcount underflow");
#endif

    if (old_refcnt != 1) {
        return;
    }

    /*
     * Final destruction should happen from an attached Python thread. If that
     * contract is violated, avoid Python C-API calls and leak Python refs
     * rather than risking a crash.
     */
    if (tl_py_attached_to_interp(ctx) &&
        tl_py_pins_count(ctx) == 0) {
        (void)tl_py_drain_retired(ctx, 1);
        tl_py_live_release_all(ctx);
    } else {
        const char* reason = "no attached Python thread state";
        if (tl_py_current_interp_or_null() != NULL) {
            reason = "wrong interpreter or active pins";
        }
        tl_py_handle_ctx_warn_unsafe_destroy(
            ctx,
            reason);
    }

    int heap_allocated = ctx->heap_allocated;
    tl_py_handle_ctx_destroy(ctx);
    if (heap_allocated) {
        PyMem_Free(ctx);
    }
}

void tl_py_handle_ctx_destroy(tl_py_handle_ctx_t* ctx)
{
    if (ctx == NULL) {
        return;
    }

    /* By the lifetime invariant in py_handle.h, refcount cannot reach zero
     * while any thread is still inside a ctx-protected section, so it is safe
     * to tear the mutexes down here. Deinit is NULL-safe on 3.12. */
    tl_py_mutex_deinit(&ctx->live_lock);
    tl_py_mutex_deinit(&ctx->pin_lock);

    /* Warn on leaked resources (cannot DECREF without owning thread state). */
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
    atomic_store_explicit(&ctx->live_tracking_failed, 0,
                          memory_order_relaxed);
}

/*===========================================================================
 * Pin Tracking Implementation
 *
 * Memory ordering rationale:
 * - RELAXED on increment: gating counter only; Timelog snapshot provides sync
 * - RELEASE on decrement: ensures drain sees all our iterator operations
 *
 * Python thread-state requirement:
 * - pins_exit_and_maybe_drain must run on the owning interpreter with an
 *   attached thread state (it may call drain and DECREF Python objects).
 *===========================================================================*/

void tl_py_pins_enter(tl_py_handle_ctx_t* ctx)
{
    /* RELAXED: snapshot acquisition provides the actual data barrier. pin_lock
     * serializes this zero->nonzero transition against drain list claiming. */
    TL_PY_MUTEX_LOCK(&ctx->pin_lock);
    atomic_fetch_add_explicit(&ctx->pins, 1, memory_order_relaxed);
    TL_PY_MUTEX_UNLOCK(&ctx->pin_lock);
}

void tl_py_pins_exit_and_maybe_drain(tl_py_handle_ctx_t* ctx)
{
#ifndef NDEBUG
    assert(tl_py_attached_to_interp(ctx) &&
           "tl_py_pins_exit_and_maybe_drain requires owning interpreter");
#endif

    tl_py_drop_node_t* list = NULL;
    int began_drain = 0;

    TL_PY_MUTEX_LOCK(&ctx->pin_lock);
    uint64_t old_pins = atomic_fetch_sub_explicit(
        &ctx->pins, 1, memory_order_release);

#ifndef NDEBUG
    assert(old_pins > 0 &&
           "Pin underflow: exit called without matching enter");
#endif

    /* Last pin holder: opportunistically drain retired objects. Claim the
     * retired list before releasing pin_lock, otherwise another thread could
     * enter a new pinned snapshot between the zero observation and the claim. */
    if (old_pins == 1 && tl_py_attached_to_interp(ctx) &&
        atomic_load_explicit(&ctx->retired_head, memory_order_relaxed) != NULL) {
        began_drain = tl_py_try_begin_drain_and_claim_locked(ctx, 0, &list);
    }
    TL_PY_MUTEX_UNLOCK(&ctx->pin_lock);

    if (list != NULL) {
        (void)tl_py_process_retired_list(ctx, list, 0);
    }
    if (began_drain) {
        tl_py_end_drain(ctx);
    }
}

uint64_t tl_py_pins_count(const tl_py_handle_ctx_t* ctx)
{
    /* Cast away const: atomic_load does not modify semantic state. */
    return atomic_load_explicit(
        (_Atomic(uint64_t)*)&ctx->pins,
        memory_order_relaxed);
}

/*===========================================================================
 * On-Drop Callback Implementation
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

    /* libc malloc -- no GIL held, cannot use Python allocators. */
    tl_py_drop_node_t* node = (tl_py_drop_node_t*)malloc(sizeof(*node));
    if (node == NULL) {
        /* Leak the object rather than risk UAF without GIL. */
        atomic_fetch_add_explicit(&ctx->alloc_failures, 1, memory_order_relaxed);
        return;
    }

    /* Initialize fields before CAS publication. */
    node->obj = tl_py_handle_decode(handle);
    node->ts = ts;

    /* Single-node push (head == tail); ACQ_REL rationale in tl_py_retired_push. */
    tl_py_retired_push(ctx, node, node);

    /* Metrics counter (relaxed). */
    atomic_fetch_add_explicit(&ctx->retired_count, 1, memory_order_relaxed);
}

/*===========================================================================
 * Drain Implementation
 *
 * PRECONDITION: Caller runs on the owning interpreter with an attached
 * Python thread state.
 * Performs deferred Py_DECREF for retired objects on that thread.
 *===========================================================================*/

size_t tl_py_drain_retired(tl_py_handle_ctx_t* ctx, int force)
{
#ifndef NDEBUG
    assert(tl_py_attached_to_interp(ctx) &&
           "tl_py_drain_retired requires owning interpreter");
#endif

    /* Fast path: an opportunistic (non-force) drain skips the lock + claim
     * when the retired stack is observably empty. A producer pushing
     * concurrently with this relaxed load simply leaves the work for the next
     * drain — the node is never lost (it stays on the stack until a later
     * drain or the force=1 teardown claims it). */
    if (!force &&
        atomic_load_explicit(&ctx->retired_head, memory_order_relaxed) == NULL) {
        return 0;
    }

    tl_py_drop_node_t* list = NULL;
    int began_drain = 0;

    TL_PY_MUTEX_LOCK(&ctx->pin_lock);
    began_drain = tl_py_try_begin_drain_and_claim_locked(ctx, force, &list);
    TL_PY_MUTEX_UNLOCK(&ctx->pin_lock);

    if (!began_drain) {
        return 0;
    }

    size_t count = tl_py_process_retired_list(ctx, list, force);
    tl_py_end_drain(ctx);
    return count;
}

/*===========================================================================
 * Live Handle Tracking (multiset) Implementation
 *
 * The _locked helpers contain the pure table operations; callers must hold
 * ctx->live_lock. The public _note_* wrappers take the lock around them.
 *
 * Hard rule: no Py_DECREF, warning, weakref callback or any other code
 * that may execute Python may run while live_lock is held — otherwise a
 * __del__ that touches the same context would deadlock or reenter the
 * table mid-mutation. release_all and traverse therefore build a local
 * array of strong references under the lock, then drop the lock before
 * Py_DECREF or visit() touches each entry.
 *===========================================================================*/

static tl_status_t tl_py_live_insert_locked(tl_py_handle_ctx_t* ctx, PyObject* obj)
{
    tl_status_t st = tl_py_live_ensure(ctx, 1);
    if (st != TL_OK) {
        atomic_store_explicit(&ctx->live_tracking_failed, 1, memory_order_release);
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

static void tl_py_live_drop_locked(tl_py_handle_ctx_t* ctx, PyObject* obj)
{
    if (ctx->live_cap == 0) {
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

tl_status_t tl_py_live_note_insert(tl_py_handle_ctx_t* ctx, PyObject* obj)
{
#ifndef NDEBUG
    assert(tl_py_attached_to_interp(ctx) &&
           "tl_py_live_note_insert requires owning interpreter");
#endif

    if (ctx == NULL || obj == NULL) {
        return TL_EINVAL;
    }

    TL_PY_MUTEX_LOCK(&ctx->live_lock);
    tl_status_t st = tl_py_live_insert_locked(ctx, obj);
    TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
    return st;
}

void tl_py_live_note_drop(tl_py_handle_ctx_t* ctx, PyObject* obj)
{
#ifndef NDEBUG
    assert(tl_py_attached_to_interp(ctx) &&
           "tl_py_live_note_drop requires owning interpreter");
#endif

    if (ctx == NULL || obj == NULL) {
        return;
    }

    TL_PY_MUTEX_LOCK(&ctx->live_lock);
    tl_py_live_drop_locked(ctx, obj);
    TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
}

void tl_py_live_release_all(tl_py_handle_ctx_t* ctx)
{
#ifndef NDEBUG
    assert(tl_py_attached_to_interp(ctx) &&
           "tl_py_live_release_all requires owning interpreter");
#endif

    if (ctx == NULL) {
        return;
    }

    PyObject** refs = NULL;
    size_t total = 0;

    /* Phase 1: collect strong refs under live_lock; free the table. */
    TL_PY_MUTEX_LOCK(&ctx->live_lock);
    if (ctx->live_entries == NULL) {
        TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
        return;
    }

#ifndef NDEBUG
    if (atomic_load_explicit(&ctx->live_tracking_failed,
                             memory_order_acquire)) {
        fprintf(stderr,
            "WARNING: live handle tracking encountered allocation failures; "
            "some objects may leak.\n");
    }
#endif

    /* Two-pass: count the multiset total (live_len counts distinct
     * entries; total refs = sum of e->count over FULL entries). */
    size_t needed = 0;
    for (size_t i = 0; i < ctx->live_cap; i++) {
        tl_py_live_entry_t* e = &ctx->live_entries[i];
        if (e->state == TL_PY_LIVE_FULL) {
            needed += (size_t)e->count;
        }
    }

    if (needed > 0) {
        /* libc malloc, not PyMem_*: the latter can acquire CPython's
         * internal allocator lock and reach back into Python state, which
         * is forbidden while we still hold live_lock. */
        refs = (PyObject**)malloc(needed * sizeof(PyObject*));
        if (refs == NULL) {
            /* OOM. We must not Py_DECREF under live_lock, so the only safe
             * option is to drop the entries here and let the payloads leak
             * until interpreter teardown. The ctx is being destroyed
             * anyway; the alternative is deadlock or UAF via __del__. */
            atomic_store_explicit(&ctx->live_tracking_failed, 1,
                                  memory_order_release);
            for (size_t i = 0; i < ctx->live_cap; i++) {
                tl_py_live_entry_t* e = &ctx->live_entries[i];
                e->obj = NULL;
                e->count = 0;
                e->state = TL_PY_LIVE_EMPTY;
            }
            free(ctx->live_entries);
            ctx->live_entries = NULL;
            ctx->live_cap = 0;
            ctx->live_len = 0;
            ctx->live_tombstones = 0;
            TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
#ifndef NDEBUG
            fprintf(stderr,
                "WARNING: tl_py_live_release_all OOM during snapshot; "
                "deliberately leaked tracked PyObjects.\n");
#endif
            return;
        }
    }

    for (size_t i = 0; i < ctx->live_cap; i++) {
        tl_py_live_entry_t* e = &ctx->live_entries[i];
        if (e->state == TL_PY_LIVE_FULL) {
            for (uint64_t c = e->count; c > 0; c--) {
                refs[total++] = e->obj;
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
    TL_PY_MUTEX_UNLOCK(&ctx->live_lock);

    /* Phase 2: Py_DECREF outside live_lock. __del__ may reenter Python
     * freely now that no internal lock is held. */
    for (size_t i = 0; i < total; i++) {
        Py_DECREF(refs[i]);
    }
    free(refs);
}

int tl_py_handle_ctx_traverse(tl_py_handle_ctx_t* ctx, visitproc visit, void* arg)
{
#ifndef NDEBUG
    assert(tl_py_attached_to_interp(ctx) &&
           "tl_py_handle_ctx_traverse requires owning interpreter");
#endif
    if (ctx == NULL || visit == NULL) {
        return 0;
    }

    PyObject** snap = NULL;
    size_t snap_n = 0;

    /* Phase 1: snapshot strong refs under live_lock. A raw pointer snapshot is
     * not enough under no-GIL: a concurrent drain can drop the last reference
     * immediately after we unlock, before visit() sees the pointer. */
    TL_PY_MUTEX_LOCK(&ctx->live_lock);
    if (ctx->live_entries != NULL && ctx->live_len > 0) {
        snap = (PyObject**)malloc(ctx->live_len * sizeof(PyObject*));
        if (snap == NULL) {
            TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
            PyErr_NoMemory();
            return -1;
        } else {
            for (size_t i = 0; i < ctx->live_cap; i++) {
                tl_py_live_entry_t* e = &ctx->live_entries[i];
                if (e->state == TL_PY_LIVE_FULL && e->obj != NULL) {
                    Py_INCREF(e->obj);
                    snap[snap_n++] = e->obj;
                }
            }
        }
    }
    TL_PY_MUTEX_UNLOCK(&ctx->live_lock);

    /* Phase 2: visit live snapshot outside live_lock. */
    int rc = 0;
    for (size_t i = 0; i < snap_n; i++) {
        rc = visit(snap[i], arg);
        if (rc != 0) {
            break;
        }
    }
    for (size_t i = 0; i < snap_n; i++) {
        Py_DECREF(snap[i]);
    }
    free(snap);
    if (rc != 0) {
        return rc;
    }

    /*
     * The retired Treiber stack is deliberately NOT walked here. Walking it
     * would read node->next non-atomically while a concurrent
     * tl_py_drain_retired() on another thread atomically claims the list and
     * free()s the nodes — a use-after-free under free-threaded builds where
     * tp_traverse can be invoked outside a stop-the-world collection (e.g.
     * gc.get_referents() / gc.get_objects()).
     *
     * This loses nothing for GC correctness: an object enters the retired
     * stack via on_drop_handle but is removed from the live table only later,
     * during drain (tl_py_live_note_drop). So every retired-but-not-drained
     * object that was successfully live-tracked is still reported by the
     * Phase-1 live-table walk above. Objects that were never tracked (insert
     * OOM) are already best-effort and may leak — acceptable, and not a
     * UAF.
     */
    return 0;
}

/*===========================================================================
 * Metrics Implementation
 *===========================================================================*/

uint64_t tl_py_retired_queue_len(const tl_py_handle_ctx_t* ctx)
{
    /* Approximate: may briefly undercount during batch re-attachment. */
    uint64_t retired = atomic_load_explicit(
        (_Atomic(uint64_t)*)&ctx->retired_count,
        memory_order_relaxed);
    uint64_t drained = atomic_load_explicit(
        (_Atomic(uint64_t)*)&ctx->drained_count,
        memory_order_relaxed);

    /* Defensive underflow protection. */
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
