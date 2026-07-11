#ifndef TIMELOGPY_PY_COMPAT_H
#define TIMELOGPY_PY_COMPAT_H

#include <Python.h>
#include <pythread.h>

/* Python 3.12 fallback for Py_IsFinalizing (3.13+ public API). */
#if PY_VERSION_HEX < 0x030D0000
static inline int tl_py_is_finalizing_compat(void)
{
    PyObject* func = PySys_GetObject("is_finalizing"); /* borrowed */
    if (func == NULL) {
        return 1;
    }
    PyObject* res = PyObject_CallNoArgs(func);
    if (res == NULL) {
        PyErr_Clear();
        return 1;
    }
    int is_final = PyObject_IsTrue(res);
    Py_DECREF(res);
    if (is_final < 0) {
        PyErr_Clear();
        return 1;
    }
    return is_final;
}
#define TL_PY_IS_FINALIZING() tl_py_is_finalizing_compat()
#else
#define TL_PY_IS_FINALIZING() Py_IsFinalizing()
#endif

/*===========================================================================
 * Mutex compat — PyMutex (3.13+) vs PyThread_type_lock fallback (3.12)
 *
 * Both branches expose:
 *   tl_py_mutex_t           opaque storage type (embed by value)
 *   tl_py_mutex_init(m)     returns 0 on success, -1 on failure
 *   tl_py_mutex_deinit(m)   releases resources (NULL-safe)
 *   TL_PY_MUTEX_LOCK(m)     blocking acquire
 *   TL_PY_MUTEX_UNLOCK(m)   release
 *
 * Memory model:
 *   Acquire is a full memory barrier; release pairs with acquire on any
 *   other thread's acquire of the same mutex. PyMutex (3.13+) and
 *   PyThread_type_lock both honor this.
 *
 * Failure model:
 *   PyMutex is statically zero-initializable so init cannot fail on 3.13+.
 *   The 3.12 fallback allocates a PyThread_type_lock and CAN fail;
 *   callers MUST check the int return.
 *===========================================================================*/

#if PY_VERSION_HEX >= 0x030D0000

typedef PyMutex tl_py_mutex_t;

static inline int tl_py_mutex_init(tl_py_mutex_t* m)
{
    /* PyMutex is statically zero-initializable. Be explicit. */
    PyMutex zero = {0};
    *m = zero;
    return 0;
}
static inline void tl_py_mutex_deinit(tl_py_mutex_t* m)
{
    (void)m; /* PyMutex needs no explicit teardown. */
}
#define TL_PY_MUTEX_LOCK(m)   PyMutex_Lock(m)
#define TL_PY_MUTEX_UNLOCK(m) PyMutex_Unlock(m)

/* Non-blocking acquire: succeed only from the fully-unlocked state. This is
 * exactly PyMutex_Lock's documented inline fast path (cpython/lock.h: CAS
 * _bits UNLOCKED->LOCKED) minus the parking slow path. Used by tp_traverse,
 * which must NEVER park: during a free-threaded stop-the-world collection
 * the lock holder may be a frozen thread that cannot run to release it. */
static inline int tl_py_mutex_trylock(tl_py_mutex_t* m)
{
    uint8_t expected = _Py_UNLOCKED;
    return _Py_atomic_compare_exchange_uint8(&m->_bits, &expected, _Py_LOCKED);
}

#else /* PY_VERSION_HEX < 0x030D0000 */

typedef PyThread_type_lock tl_py_mutex_t;

static inline int tl_py_mutex_init(tl_py_mutex_t* m)
{
    *m = PyThread_allocate_lock();
    return *m == NULL ? -1 : 0;
}
static inline void tl_py_mutex_deinit(tl_py_mutex_t* m)
{
    if (*m != NULL) {
        PyThread_free_lock(*m);
        *m = NULL;
    }
}
#define TL_PY_MUTEX_LOCK(m)   ((void)PyThread_acquire_lock(*(m), WAIT_LOCK))
#define TL_PY_MUTEX_UNLOCK(m) PyThread_release_lock(*(m))

static inline int tl_py_mutex_trylock(tl_py_mutex_t* m)
{
    return PyThread_acquire_lock(*(m), NOWAIT_LOCK) == PY_LOCK_ACQUIRED;
}

#endif /* PY_VERSION_HEX */

/*===========================================================================
 * Critical-section compat — Py_BEGIN_CRITICAL_SECTION (3.13+)
 *
 * Use these around mutable extension-object field accesses that need to be
 * serialized when multiple Python threads may touch the same object. On
 * 3.12 the macros are no-ops because the GIL serializes all object access;
 * heap-type registration keeps a single PyTimelog instance bound to one
 * interpreter, so cross-interpreter concurrency cannot occur there either.
 *
 * INVARIANT (PEP 703):
 *   Critical sections do NOT pin their target via refcount. They take an
 *   internal per-object mutex. The caller MUST already hold a strong
 *   Python reference to the target object for the full duration of
 *   TL_PY_OBJ_LOCK ... TL_PY_OBJ_UNLOCK. For methods invoked via Python's
 *   bound-method dispatch this is automatic — the dispatch holds an
 *   implicit ref on `self`. For C-internal callers (factory helpers,
 *   release hooks), an explicit Py_INCREF before TL_PY_OBJ_LOCK is
 *   REQUIRED. Failing this is an immediate UAF risk under free-threaded
 *   builds.
 *
 * SCOPE:
 *   Critical sections are leaf scopes. Do NOT hold them across Py_DECREF,
 *   allocations that can run Python, warnings, finalizers, or any code
 *   that may re-enter Python and try to take a lock; doing so risks
 *   deadlock or lock-order violations.
 *
 *   Permitted under a single-object critical section:
 *     - A lone Py_INCREF / Py_NewRef of a DISTINCT object (e.g. capturing a
 *       strong ref to self->timelog/self->owner before releasing the lock).
 *       INCREF executes no Python and cannot recurse into the same object's
 *       critical section, so it is safe and is used to pin a borrowed field
 *       for use after unlock.
 *     - The pure-C engine iterator step (tl_iter_next / tl_pagespan_iter_next)
 *       is deliberately held under the iterator's own critical section: it
 *       executes no Python, acquires no lock another thread could hold while
 *       waiting on this CS, and doing so closes the close-vs-iternext UAF
 *       window. Do NOT generalize this to other tl_* calls that may block.
 *===========================================================================*/

#ifndef TL_PY_TSAN_ENABLED
#  if defined(__has_feature)
#    if __has_feature(thread_sanitizer)
#      define TL_PY_TSAN_ENABLED 1
#    endif
#  endif
#  if !defined(TL_PY_TSAN_ENABLED) && defined(__SANITIZE_THREAD__)
#    define TL_PY_TSAN_ENABLED 1
#  endif
#  if !defined(TL_PY_TSAN_ENABLED)
#    define TL_PY_TSAN_ENABLED 0
#  endif
#endif

#if TL_PY_TSAN_ENABLED
/* CPython critical sections live in libpython, which local/CI pyenv builds may
 * not compile with TSan. Mirror those synchronization edges so TSan can see the
 * protection around Timelog extension-object fields. */
void __tsan_acquire(void* addr);
void __tsan_release(void* addr);
#define TL_PY_TSAN_ACQUIRE(addr) __tsan_acquire((void*)(addr))
#define TL_PY_TSAN_RELEASE(addr) __tsan_release((void*)(addr))
#else
#define TL_PY_TSAN_ACQUIRE(addr) ((void)(addr))
#define TL_PY_TSAN_RELEASE(addr) ((void)(addr))
#endif

#if PY_VERSION_HEX >= 0x030D0000
#define TL_PY_OBJ_LOCK(obj)                                           \
    {                                                                 \
        PyObject* tl_py_cs_obj__ = (PyObject*)(obj);                  \
        Py_BEGIN_CRITICAL_SECTION(tl_py_cs_obj__);                    \
        TL_PY_TSAN_ACQUIRE(tl_py_cs_obj__)
#define TL_PY_OBJ_UNLOCK()                                            \
        TL_PY_TSAN_RELEASE(tl_py_cs_obj__);                           \
        Py_END_CRITICAL_SECTION();                                    \
    }
#define TL_PY_OBJ_LOCK2(a, b)                                         \
    {                                                                 \
        PyObject* tl_py_cs_obj1__ = (PyObject*)(a);                   \
        PyObject* tl_py_cs_obj2__ = (PyObject*)(b);                   \
        Py_BEGIN_CRITICAL_SECTION2(tl_py_cs_obj1__, tl_py_cs_obj2__); \
        TL_PY_TSAN_ACQUIRE(tl_py_cs_obj1__);                          \
        TL_PY_TSAN_ACQUIRE(tl_py_cs_obj2__)
#define TL_PY_OBJ_UNLOCK2()                                           \
        TL_PY_TSAN_RELEASE(tl_py_cs_obj2__);                          \
        TL_PY_TSAN_RELEASE(tl_py_cs_obj1__);                          \
        Py_END_CRITICAL_SECTION2();                                   \
    }
#else
/* GIL-serialized fallback. (void) casts suppress unused-arg warnings. */
#define TL_PY_OBJ_LOCK(obj)   do { (void)(obj);
#define TL_PY_OBJ_UNLOCK()    } while (0)
#define TL_PY_OBJ_LOCK2(a, b) do { (void)(a); (void)(b);
#define TL_PY_OBJ_UNLOCK2()   } while (0)
#endif

/*===========================================================================
 * Shared object idioms
 *===========================================================================*/

/*
 * Standard tp_dealloc epilogue for a GC-tracked heap type: capture the type,
 * untrack, run the type-specific cleanup, free the instance, then drop the
 * reference the instance held on its (heap) type. Centralizing this keeps the
 * easy-to-forget Py_DECREF(tp) correct across every heap type. cleanup_stmt is
 * a single statement (no trailing semicolon) and runs after untrack, before
 * the instance is freed.
 */
#define TL_PY_GC_DEALLOC(self, cleanup_stmt)             \
    do {                                                 \
        PyTypeObject* tl_dealloc_tp__ = Py_TYPE(self);   \
        PyObject_GC_UnTrack(self);                       \
        cleanup_stmt;                                    \
        tl_dealloc_tp__->tp_free((PyObject*)(self));     \
        Py_DECREF(tl_dealloc_tp__);                      \
    } while (0)

/*
 * Define a read-only `closed` boolean getter that samples self->closed under
 * the per-object critical section. Used by the iterator/span heap types whose
 * `closed` flag is a plain field guarded by TL_PY_OBJ_LOCK (PyTimelog's is
 * _Atomic and intentionally keeps its own getter).
 */
#define TL_PY_DEFINE_CLOSED_GETTER(Fn, Type)             \
    static PyObject* Fn(Type* self, void* closure)       \
    {                                                    \
        (void)closure;                                   \
        int closed;                                      \
        TL_PY_OBJ_LOCK(self);                            \
        closed = self->closed;                           \
        TL_PY_OBJ_UNLOCK();                              \
        return PyBool_FromLong(closed);                  \
    }

/*
 * Define a read-only int64 timestamp getter over a PageSpan-style field that
 * is immutable after construction: sample `closed` and the field under the
 * per-object critical section, raise the closed ValueError outside it.
 * (Sibling of TL_PY_DEFINE_CLOSED_GETTER; the field type is tl_ts_t at every
 * expansion site.)
 */
#define TL_PY_DEFINE_SPAN_TS_GETTER(Fn, Type, field)     \
    static PyObject* Fn(Type* self, void* closure)       \
    {                                                    \
        (void)closure;                                   \
        int closed;                                      \
        long long v;                                     \
        TL_PY_OBJ_LOCK(self);                            \
        closed = self->closed;                           \
        v = (long long)self->field;                      \
        TL_PY_OBJ_UNLOCK();                              \
        if (closed) {                                    \
            PyErr_SetString(PyExc_ValueError,            \
                            "PageSpan is closed");       \
            return NULL;                                 \
        }                                                \
        return PyLong_FromLongLong(v);                   \
    }

/*
 * Shared __enter__ for context-manager heap types whose entry is exactly
 * "return self" (PageSpan, TimelogIter, PageSpanIter). PyTimelog's __enter__
 * is deliberately NOT a user — it also restarts maintenance.
 */
static inline PyObject* tl_py_enter_self(PyObject* self, PyObject* noargs)
{
    (void)noargs;
    return Py_NewRef(self);
}

#endif /* TIMELOGPY_PY_COMPAT_H */
