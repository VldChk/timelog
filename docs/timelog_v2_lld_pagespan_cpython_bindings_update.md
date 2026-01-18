# LLD: CPython PageSpan Bindings on Core PageSpan Iterator

Status: **approved** (implementation driver)
Last revised: 2026-01-22

This document specifies the **binding-side changes** required to adopt the
core PageSpan iterator API (`tl_pagespan_iter_*`) in CPython. The goal is to
remove algorithm duplication in `py_span_iter.c` while preserving B4 behavior
(zero-copy timestamps, pins-based lifetime safety, and Python-facing API
compatibility).

---

## 1. Problem Statement

The current CPython PageSpan bindings re-implement range pruning and span
collection by walking `tl_snapshot_t`, `tl_manifest_t`, `tl_segment_t`, and
`tl_page_t` directly. This duplicates core logic and couples bindings to
storage internals.

### Current Architecture (to be replaced)

Current flow (simplified):

py_span_iter.c
  - collect_spans/process_segment_catalog
  - walks manifest->l1/l0
  - uses tl_page_catalog_* helpers
  - stores span_desc_t[]
  -> duplicates algorithm in src/query/tl_pagespan_iter.c

py_span.c
  - tl_py_span_owner_t owns snapshot
  - PyPageSpan uses page pointer + row_start/row_end
  -> couples to src/storage/tl_page.h

### Target Architecture

Target flow (simplified):

py_span_iter.c
  - holds tl_pagespan_iter_t
  - calls tl_pagespan_iter_open/next
  - no algorithm code
  -> delegates to src/query/tl_pagespan_iter.c

py_span.c
  - uses tl_pagespan_owner_t (core)
  - PyPageSpan stores view pointers (ts/h/len)
  -> depends only on tl_pagespan_view_t

A new core API (`src/query/tl_pagespan_iter.h/.c`) now provides the canonical
span iterator and view layout. The binding must delegate iteration and ownership
handling to the core API and **avoid re-implementing range logic**.

---

## 2. Goals

- Use `tl_pagespan_iter_open/next/close` for all span enumeration.
- Preserve the Python API (`Timelog.page_spans`, `PageSpan`, `PageSpanIter`).
- Preserve B4 lifetime safety: pins must remain held until the last span is
  released.
- Keep zero-copy timestamp exposure via the buffer protocol.
- Reduce coupling to core storage internals (no direct use of `tl_page_t`
  layout except through `tl_pagespan_view_t` pointers).

## 3. Non-goals

- Change Python API signatures or behavior beyond current B4 expectations.
- Implement memview/memtable spans (B4 remains segments-only).
- Change core pagespan iterator behavior or flags.

---

## 4. Python API Surface (unchanged)

- `Timelog.page_spans(t1, t2, *, kind='segment') -> PageSpanIter`
- `PageSpan` properties: `timestamps`, `start_ts`, `end_ts`, `closed`, `len()`
- `PageSpan` methods: `close()`, `objects()`, `copy_timestamps()`, `copy()`
- `PageSpanIter` iteration and `close()`
- `PageSpanObjectsView` sequence/iterator behavior

The binding continues to accept `kind='segment'` only. Unsupported values raise
`ValueError`.

---

## 5. Core API Reference

The binding uses these core types and functions from `query/tl_pagespan_iter.h`:

### 5.1 Types

```c
/* Opaque owner - pins resources until all spans released */
typedef struct tl_pagespan_owner tl_pagespan_owner_t;

/* Opaque iterator over spans */
typedef struct tl_pagespan_iter tl_pagespan_iter_t;

/* Span view - returned by iter_next */
typedef struct tl_pagespan_view {
    tl_pagespan_owner_t* owner;     /* Owned ref (caller must decref) */
    const tl_ts_t*       ts;        /* Pointer to timestamp array */
    const tl_handle_t*   h;         /* Pointer to handle array */
    uint32_t             len;       /* Row count (always > 0) */
    tl_ts_t              first_ts;  /* == ts[0] */
    tl_ts_t              last_ts;   /* == ts[len-1] */
} tl_pagespan_view_t;

/* Release hooks for binding cleanup */
typedef void (*tl_pagespan_owner_release_fn)(void* user);
typedef struct tl_pagespan_owner_hooks {
    void* user;
    tl_pagespan_owner_release_fn on_release;
} tl_pagespan_owner_hooks_t;
```

### 5.2 Functions

```c
tl_status_t tl_pagespan_iter_open(
    tl_timelog_t* tl,
    tl_ts_t t1, tl_ts_t t2,
    uint32_t flags,
    const tl_pagespan_owner_hooks_t* hooks,
    tl_pagespan_iter_t** out);

tl_status_t tl_pagespan_iter_next(
    tl_pagespan_iter_t* it,
    tl_pagespan_view_t* out_view);

void tl_pagespan_iter_close(tl_pagespan_iter_t* it);

void tl_pagespan_owner_incref(tl_pagespan_owner_t* owner);
void tl_pagespan_owner_decref(tl_pagespan_owner_t* owner);

static inline void tl_pagespan_view_release(tl_pagespan_view_t* v);
```

### 5.3 Flags

```c
#define TL_PAGESPAN_DEFAULT \
    (TL_PAGESPAN_SEGMENTS_ONLY | TL_PAGESPAN_INCLUDE_L0 | \
     TL_PAGESPAN_INCLUDE_L1 | TL_PAGESPAN_REQUIRE_ZEROCOPY)
```

---

## 6. Binding Data Structures

### 6.1 PyPageSpanIter (BEFORE)

```c
typedef struct {
    PyObject_HEAD
    tl_py_span_owner_t* owner;  /* binding's own owner type */
    span_desc_t* spans;         /* pre-collected array */
    size_t count;               /* total spans */
    size_t index;               /* iteration position */
    uint8_t closed;
} PyPageSpanIter;
```

### 6.2 PyPageSpanIter (AFTER)

Replace precomputed span arrays with a core iterator pointer:

```c
typedef struct {
    PyObject_HEAD
    tl_pagespan_iter_t* iter;   /* core iterator (owned) */
    PyObject* timelog;          /* strong ref for GC visibility */
    uint8_t closed;
} PyPageSpanIter;
```

No span descriptors are stored in Python. Iteration is streaming.

### 6.3 PyPageSpan (BEFORE)

```c
typedef struct {
    PyObject_HEAD
    tl_py_span_owner_t* owner;  /* binding's own owner */
    const tl_page_t* page;      /* borrowed page pointer */
    size_t row_start;           /* inclusive */
    size_t row_end;             /* exclusive */
    Py_ssize_t shape[1];
    Py_ssize_t strides[1];
    uint32_t exports;
    uint8_t closed;
} PyPageSpan;
```

### 6.4 PyPageSpan (AFTER)

Store view pointers instead of a `tl_page_t*` and row indices:

```c
typedef struct {
    PyObject_HEAD
    tl_pagespan_owner_t* owner; /* core owner (owned ref) */
    PyObject* timelog;          /* strong ref for GC visibility */
    const tl_ts_t* ts;          /* view->ts (borrowed from owner's snapshot) */
    const tl_handle_t* h;       /* view->h (may be NULL if unsupported) */
    uint32_t len;               /* view->len */
    tl_ts_t first_ts;           /* view->first_ts (cached) */
    tl_ts_t last_ts;            /* view->last_ts (cached) */
    Py_ssize_t shape[1];
    Py_ssize_t strides[1];
    uint32_t exports;
    uint8_t closed;
} PyPageSpan;
```

**Ownership rule:** `PyPageSpan_FromView` *consumes* the view's owner reference
(no extra incref) and sets `view->owner = NULL` on success. On failure, the
caller must call `tl_pagespan_view_release`.

---

## 7. Core API Mapping

### 7.1 Open

Binding logic calls the core iterator directly. The core now always creates an
owner (even for empty ranges), so the binding uses one unified path for all
ranges.

```c
// In PyPageSpanIter_Create
PyObject* PyPageSpanIter_Create(PyObject* timelog,
                                tl_ts_t t1,
                                tl_ts_t t2,
                                const char* kind)
{
    /* Validate kind parameter */
    if (strcmp(kind, "segment") != 0) {
        PyErr_Format(PyExc_ValueError,
            "page_spans: kind must be 'segment', got '%s'", kind);
        return NULL;
    }

    PyTimelog* tl_obj = (PyTimelog*)timelog;

    /* Check if timelog is closed */
    if (tl_obj->closed || tl_obj->tl == NULL) {
        TlPy_RaiseFromStatus(TL_ESTATE);
        return NULL;
    }

    uint32_t flags = TL_PAGESPAN_DEFAULT;
    tl_pagespan_iter_t* core_iter = NULL;

    /* CRITICAL: pins_enter BEFORE iter_open
     * This closes the window where compaction could drain retired handles
     * while we're acquiring the snapshot. See py_handle.h protocol docs.
     */
    tl_py_pins_enter(&tl_obj->handle_ctx);

    /* Allocate and setup hook context */
    tl_py_pagespan_hook_ctx_t* hook_ctx = PyMem_Malloc(sizeof(*hook_ctx));
    if (!hook_ctx) {
        tl_py_pins_exit_and_maybe_drain(&tl_obj->handle_ctx);
        PyErr_NoMemory();
        return NULL;
    }
    hook_ctx->timelog = Py_NewRef((PyObject*)tl_obj);
    hook_ctx->ctx = &tl_obj->handle_ctx;
    hook_ctx->armed = 0;

    tl_pagespan_owner_hooks_t hooks = {
        .user = hook_ctx,
        .on_release = tl_py_pagespan_on_release
    };

    /* Call core iterator */

    tl_status_t st = tl_pagespan_iter_open(
        tl_obj->tl, t1, t2, flags, &hooks, &core_iter);

    if (st != TL_OK) {
        /* CRITICAL: pins_enter was called but no owner was created.
         * No release hook will run, so we must cleanup here.
         */
        Py_DECREF(hook_ctx->timelog);
        PyMem_Free(hook_ctx);
        tl_py_pins_exit_and_maybe_drain(&tl_obj->handle_ctx);
        TlPy_RaiseFromStatus(st);
        return NULL;
    }

    /* From here on, the hook owns cleanup */
    hook_ctx->armed = 1;

    /* Allocate Python iterator */
    PyPageSpanIter* self = PyObject_GC_New(PyPageSpanIter, &PyPageSpanIter_Type);
    if (!self) {
        tl_pagespan_iter_close(core_iter);
        return NULL;
    }

    self->iter = core_iter;
    self->timelog = Py_NewRef((PyObject*)tl_obj);
    self->closed = 0;

    PyObject_GC_Track((PyObject*)self);
    return (PyObject*)self;
}
```


### 7.2 Next

```c
// In tp_iternext
static PyObject* PyPageSpanIter_iternext(PyPageSpanIter* self)
{
    if (self->closed || self->iter == NULL) {
        return NULL;  /* StopIteration */
    }

    tl_pagespan_view_t view;
    memset(&view, 0, sizeof(view));

    tl_status_t st = tl_pagespan_iter_next(self->iter, &view);

    if (st == TL_OK) {
        /* Build PyPageSpan from view - consumes view's owner ref */
        PyObject* span = PyPageSpan_FromView(&view, self->timelog);
        if (!span) {
            /* Creation failed - release the owner ref we received */
            tl_pagespan_view_release(&view);
            return NULL;
        }
        return span;
    }

    if (st == TL_EOF) {
        /* Exhausted - cleanup iterator */
        pagespaniter_cleanup(self);
        return NULL;  /* StopIteration */
    }

    /* Error - cleanup and raise */
    pagespaniter_cleanup(self);
    TlPy_RaiseFromStatus(st);
    return NULL;
}
```

### 7.3 Close

`PyPageSpanIter.close()` calls `tl_pagespan_iter_close(self->iter)` and
nulls the pointer. The core iterator releases its owner ref. Returned spans
remain valid while their owner refs remain live.

```c
static void pagespaniter_cleanup(PyPageSpanIter* self)
{
    if (self->closed) {
        return;
    }
    self->closed = 1;

    tl_pagespan_iter_t* iter = self->iter;
    self->iter = NULL;

    if (iter) {
        tl_pagespan_iter_close(iter);
    }

    Py_CLEAR(self->timelog);
}
```

---

## 8. Lifetime Integration (Pins + Owner Release Hook)

The core owner is opaque and releases its resources when the last reference
is dropped. The binding must attach a release hook that drops pins and releases
its strong `PyTimelog` reference.

### 8.1 Hook Context

```c
typedef struct tl_py_pagespan_hook_ctx {
    PyObject* timelog;          /* strong ref, decref on release */
    tl_py_handle_ctx_t* ctx;    /* borrowed handle context */
    int armed;                  /* 0 until iter_open succeeds */
} tl_py_pagespan_hook_ctx_t;
```

The hook context is allocated with `PyMem_Malloc` and freed in the hook.
The `armed` flag prevents double cleanup if the core calls the hook during
`tl_pagespan_iter_open` failure paths.

### 8.2 Hook Function

```c
static void tl_py_pagespan_on_release(void* user) {
    tl_py_pagespan_hook_ctx_t* ctx = (tl_py_pagespan_hook_ctx_t*)user;
    if (ctx == NULL) return;
    if (!ctx->armed) {
        return;  /* iter_open failed after owner creation; binding cleans up */
    }

    /*
     * GIL INVARIANT: This hook is ONLY called from owner_decref, which is
     * ONLY called from CPython code paths (tp_dealloc, close(), etc.).
     * All such paths hold the GIL. If future refactors allow decref from
     * background threads, this hook MUST use PyGILState_Ensure/Release.
     */

    /*
     * EXCEPTION PRESERVATION: The hook may run during GC/unwinding when an
     * exception is already set. Py_DECREF can run arbitrary finalizers that
     * might clobber exception state. Save and restore to avoid losing the
     * user's exception context.
     */
    PyObject *exc_type, *exc_value, *exc_tb;
    PyErr_Fetch(&exc_type, &exc_value, &exc_tb);

    if (ctx->ctx) {
        tl_py_pins_exit_and_maybe_drain(ctx->ctx);
    }

    Py_XDECREF(ctx->timelog);
    PyMem_Free(ctx);

    PyErr_Restore(exc_type, exc_value, exc_tb);
}
```

Armed handshake: `hook_ctx->armed` is set to 1 only after
`tl_pagespan_iter_open` returns `TL_OK`. This prevents double cleanup if
`iter_open` fails after creating the owner (the core may invoke the hook
before returning the error, but the hook is inert until armed).

### 8.3 Hook Setup in `PyPageSpanIter_Create`

- Call `tl_py_pins_enter(&tl->handle_ctx)` before `tl_pagespan_iter_open`.
- Allocate hook ctx; store `Py_NewRef(timelog)`, handle_ctx pointer, and set `armed = 0`.
- On open failure: free ctx, decref timelog, `tl_py_pins_exit_and_maybe_drain`, raise.
- On success: set `armed = 1`; core owns the hook and will call it when the
  owner refcount reaches zero.

**GIL requirement:** The hook must only run when the GIL is held. The binding
ensures `tl_pagespan_owner_decref` and `tl_pagespan_iter_close` are only called
from Python-visible paths (GIL held).

### 8.4 Lifetime Diagram

```
PyPageSpanIter_Create:
    pins_enter()
    allocate hook_ctx
    tl_pagespan_iter_open() -> creates owner with refcnt=1
    hook_ctx->armed = 1

PyPageSpanIter.tp_iternext:
    tl_pagespan_iter_next() -> incref owner, return view
    PyPageSpan_FromView(view, timelog) -> consumes owner ref

PyPageSpan.close() / tp_dealloc:
    tl_pagespan_owner_decref()
        if refcnt -> 0:
            release snapshot
            free owner struct
            call on_release hook:
                pins_exit_and_maybe_drain()
                Py_DECREF(timelog)
                PyMem_Free(hook_ctx)
```

---

## 9. PyPageSpan Creation from View

### 9.1 Factory Function

```c
/* Creates PyPageSpan from a view, CONSUMING the view's owner reference.
 * On success, the span owns the reference and view->owner is set to NULL.
 * On failure, caller must call tl_pagespan_view_release().
 */
PyObject* PyPageSpan_FromView(tl_pagespan_view_t* view, PyObject* timelog)
{
    if (!view || !view->owner) {
        PyErr_SetString(PyExc_RuntimeError, "invalid view");
        return NULL;
    }
    if (timelog == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "timelog is NULL");
        return NULL;
    }

    PyPageSpan* self = PyObject_GC_New(PyPageSpan, &PyPageSpan_Type);
    if (!self) {
        return NULL;
    }

    /* Transfer ownership - no incref needed (view's ref is consumed) */
    self->owner = view->owner;
    view->owner = NULL;  /* prevent accidental double-decref */
    self->timelog = Py_NewRef(timelog);
    self->ts = view->ts;
    self->h = view->h;
    self->len = view->len;
    self->first_ts = view->first_ts;
    self->last_ts = view->last_ts;
    self->shape[0] = 0;
    self->strides[0] = 0;
    self->exports = 0;
    self->closed = 0;

    PyObject_GC_Track((PyObject*)self);
    return (PyObject*)self;
}
```

### 9.2 Cleanup

```c
static void pagespan_cleanup(PyPageSpan* self)
{
    if (self->closed) {
        return;
    }
    self->closed = 1;

    /* Clear borrowed pointers */
    self->ts = NULL;
    self->h = NULL;

    /* Release owner reference */
    tl_pagespan_owner_t* owner = self->owner;
    self->owner = NULL;

    if (owner) {
        tl_pagespan_owner_decref(owner);
    }

    Py_CLEAR(self->timelog);
}
```

---

## 10. Buffer Protocol Changes

The buffer protocol uses `span->ts` and `span->len`:

Exporter contract highlights:
- On success, `view->obj` is a NEW reference to the exporter.
- On error, `view->obj` must be NULL.
- Reject `PyBUF_WRITABLE` (read-only buffer).
- Always fill request-independent fields: `obj`, `buf`, `len`, `itemsize`, `ndim`.

```c
static int pagespan_getbuffer(PyObject* exporter, Py_buffer* view, int flags)
{
    PyPageSpan* self = (PyPageSpan*)exporter;

    /* CPython contract: on error, view->obj must be NULL */
    view->obj = NULL;

    if (self->closed || self->ts == NULL) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return -1;
    }
    if (flags & PyBUF_WRITABLE) {
        PyErr_SetString(PyExc_BufferError, "PageSpan buffer is read-only");
        return -1;
    }

    const Py_ssize_t n = (Py_ssize_t)self->len;
    void* ptr = (void*)self->ts;

    /* Request-independent fields (ALWAYS set per CPython docs) */
    view->obj = Py_NewRef(exporter);
    view->buf = ptr;
    view->len = n * (Py_ssize_t)sizeof(tl_ts_t);
    view->readonly = 1;
    view->itemsize = (Py_ssize_t)sizeof(tl_ts_t);
    view->ndim = 1;

    /* Request-dependent fields */
    view->format = (flags & PyBUF_FORMAT) ? (char*)PAGESPAN_TS_FORMAT : NULL;

    if (flags & PyBUF_ND) {
        self->shape[0] = n;
        view->shape = self->shape;
    } else {
        view->shape = NULL;
    }

    if (flags & PyBUF_STRIDES) {
        self->strides[0] = (Py_ssize_t)sizeof(tl_ts_t);
        view->strides = self->strides;
    } else {
        view->strides = NULL;
    }

    view->suboffsets = NULL;
    view->internal = NULL;

    self->exports++;
    return 0;
}
```

All other semantics remain unchanged:
- read-only
- `close()` blocked while buffers exported
- `timestamps` property returns `memoryview` of the span

---

## 11. Property Getter Changes

### 11.1 BEFORE (using page pointer)

```c
static PyObject* PyPageSpan_get_start_ts(PyPageSpan* self, void* closure)
{
    if (self->closed) { /* ... */ }
    if (self->row_start >= self->row_end) { /* empty check */ }
    return PyLong_FromLongLong((long long)self->page->ts[self->row_start]);
}

static PyObject* PyPageSpan_get_end_ts(PyPageSpan* self, void* closure)
{
    if (self->closed) { /* ... */ }
    if (self->row_start >= self->row_end) { /* empty check */ }
    return PyLong_FromLongLong((long long)self->page->ts[self->row_end - 1]);
}
```

### 11.2 AFTER (using cached view fields)

```c
static PyObject* PyPageSpan_get_start_ts(PyPageSpan* self, void* closure)
{
    (void)closure;
    if (self->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }
    /* first_ts is cached from view, no pointer dereference needed */
    return PyLong_FromLongLong((long long)self->first_ts);
}

static PyObject* PyPageSpan_get_end_ts(PyPageSpan* self, void* closure)
{
    (void)closure;
    if (self->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }
    /* last_ts is cached from view, no pointer dereference needed */
    return PyLong_FromLongLong((long long)self->last_ts);
}
```

### 11.3 __len__ Changes

```c
/* BEFORE */
static Py_ssize_t PyPageSpan_length(PyPageSpan* self)
{
    if (self->closed) return 0;
    return (Py_ssize_t)(self->row_end - self->row_start);
}

/* AFTER */
static Py_ssize_t PyPageSpan_length(PyPageSpan* self)
{
    if (self->closed) return 0;
    return (Py_ssize_t)self->len;
}
```

---

## 12. GC Support Changes

### 12.1 tp_traverse

The GC traverse function must visit the timelog held indirectly. Since we no
longer have direct access to `owner->timelog` (core owner is opaque), this LLD
stores a strong timelog reference in the Python objects.

**Chosen: Store timelog reference in PyPageSpan**

```c
typedef struct {
    PyObject_HEAD
    tl_pagespan_owner_t* owner;
    PyObject* timelog;          /* Strong ref for GC visibility */
    const tl_ts_t* ts;
    const tl_handle_t* h;
    uint32_t len;
    /* ... */
} PyPageSpan;
```

```c
static int PyPageSpan_traverse(PyPageSpan* self, visitproc visit, void* arg)
{
    Py_VISIT(self->timelog);
    return 0;
}

static void pagespan_cleanup(PyPageSpan* self)
{
    if (self->closed) return;
    self->closed = 1;

    self->ts = NULL;
    self->h = NULL;

    tl_pagespan_owner_t* owner = self->owner;
    self->owner = NULL;
    if (owner) {
        tl_pagespan_owner_decref(owner);
    }

    Py_CLEAR(self->timelog);
}
```

This matches the current behavior where `span->owner->timelog` was visited.
If we later decide to drop per-span timelog refs, remove the `timelog` field
and make `tp_traverse` a no-op.

GC dealloc rule: for GC-tracked types, `tp_dealloc` must call
`PyObject_GC_UnTrack()` before clearing references or releasing the owner.

### 12.2 PyPageSpanIter tp_traverse

The iterator no longer holds a Python-visible reference chain since it holds
an opaque `tl_pagespan_iter_t*`. Store a timelog reference for GC visibility:

```c
typedef struct {
    PyObject_HEAD
    tl_pagespan_iter_t* iter;
    PyObject* timelog;          /* Strong ref for GC visibility */
    uint8_t closed;
} PyPageSpanIter;
```

---

## 13. PageSpanObjectsView Changes

### 13.1 BEFORE (accessing page->h via span)

```c
static PyObject* PyPageSpanObjectsView_getitem(PyPageSpanObjectsView* self,
                                                Py_ssize_t index)
{
    PyPageSpan* span = (PyPageSpan*)self->span;
    if (span->closed) { /* ... */ }

    Py_ssize_t len = (Py_ssize_t)(span->row_end - span->row_start);
    /* ... bounds check ... */

    tl_handle_t h = span->page->h[span->row_start + (size_t)index];
    PyObject* obj = tl_py_handle_decode(h);
    /* ... */
}
```

### 13.2 AFTER (using span->h directly)

```c
static PyObject* PyPageSpanObjectsView_getitem(PyPageSpanObjectsView* self,
                                                Py_ssize_t index)
{
    PyPageSpan* span = (PyPageSpan*)self->span;
    if (span->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    /* Check if handles are available */
    if (span->h == NULL) {
        PyErr_SetString(PyExc_ValueError, "handles not available");
        return NULL;
    }

    Py_ssize_t len = (Py_ssize_t)span->len;

    /* Handle negative indices */
    if (index < 0) {
        index += len;
    }
    if (index < 0 || index >= len) {
        PyErr_SetString(PyExc_IndexError, "index out of range");
        return NULL;
    }

    /* Direct access via span->h pointer */
    tl_handle_t h = span->h[index];
    PyObject* obj = tl_py_handle_decode(h);

    if (!obj) {
        PyErr_SetString(PyExc_RuntimeError, "invalid handle in page");
        return NULL;
    }

    return Py_NewRef(obj);
}
```

### 13.3 Length Function

```c
static Py_ssize_t PyPageSpanObjectsView_length(PyPageSpanObjectsView* self)
{
    PyPageSpan* span = (PyPageSpan*)self->span;
    if (span->closed) return 0;
    return (Py_ssize_t)span->len;
}
```

---

## 14. Error Handling

### 14.1 Core Status to Python Exception Mapping

The binding uses the existing `TlPy_RaiseFromStatus()` function which maps:
- `TL_EINVAL` -> `ValueError`
- `TL_ESTATE` -> `TimelogError`
- `TL_ENOMEM` -> `MemoryError`
- `TL_EOF` -> (handled specially, not an exception)

### 14.2 Early-Return Cleanup Pattern

```c
PyObject* PyPageSpanIter_Create(...)
{
    /* 1. Validate inputs */
    if (/* validation fails */) {
        /* No resources acquired yet */
        PyErr_SetString(...);
        return NULL;
    }

    /* 2. Enter pins */
    tl_py_pins_enter(&tl_obj->handle_ctx);

    /* 3. Allocate hook context */
    tl_py_pagespan_hook_ctx_t* hook_ctx = PyMem_Malloc(...);
    if (!hook_ctx) {
        /* Cleanup: pins */
        tl_py_pins_exit_and_maybe_drain(&tl_obj->handle_ctx);
        PyErr_NoMemory();
        return NULL;
    }
    hook_ctx->timelog = Py_NewRef((PyObject*)tl_obj);
    hook_ctx->ctx = &tl_obj->handle_ctx;

    /* 4. Call core iter_open */
    tl_status_t st = tl_pagespan_iter_open(..., &hooks, &core_iter);
    if (st != TL_OK) {
        /* Cleanup: hook_ctx, timelog ref, pins.
         * Note: core may have invoked the hook on failure, but armed==0
         * makes it a no-op, so this cleanup is safe.
         */
        Py_DECREF(hook_ctx->timelog);
        PyMem_Free(hook_ctx);
        tl_py_pins_exit_and_maybe_drain(&tl_obj->handle_ctx);
        TlPy_RaiseFromStatus(st);
        return NULL;
    }
    /* From here, hook_ctx is owned by core owner */
    hook_ctx->armed = 1;

    /* 5. Allocate Python object */
    PyPageSpanIter* self = PyObject_GC_New(...);
    if (!self) {
        /* Cleanup: core_iter (which handles hook_ctx) */
        tl_pagespan_iter_close(core_iter);
        return NULL;
    }

    /* Success path */
    self->iter = core_iter;
    self->timelog = Py_NewRef((PyObject*)tl_obj);
    self->closed = 0;
    return (PyObject*)self;
}
```

---

## 15. File-Level Change Summary

### 15.1 bindings/cpython/src/py_span_iter.c

**DELETE:**
- `collect_spans()` function (~75 lines)
- `process_segment_catalog()` function (~50 lines)
- Internal storage header includes (`tl_page.h`, `tl_segment.h`, `tl_manifest.h`)
- `tl_snapshot.h` include (no longer needed directly)

**ADD:**
- `#include "query/tl_pagespan_iter.h"`
- `tl_py_pagespan_hook_ctx_t` struct definition
- `tl_py_pagespan_on_release()` hook function
- Streaming `tl_pagespan_iter_next` in `tp_iternext`

**MODIFY:**
- `PyPageSpanIter_Create()` - replace span collection with `tl_pagespan_iter_open`
- `pagespaniter_cleanup()` - call `tl_pagespan_iter_close` instead of freeing spans
- `PyPageSpanIter_traverse()` - visit `self->timelog`
- `PyPageSpanIter` struct - replace `spans/count/index` with `iter` and `timelog`
- Hook ctx uses `armed` handshake to avoid double cleanup on iter_open failures

### 15.2 bindings/cpython/src/py_span.c

**DELETE:**
- `tl_py_span_owner_t` implementation (moved to using core's owner)
- `tl_py_span_owner_create/incref/decref` functions
- `span_owner_destroy()` function
- `PyPageSpan_Create()` function
- Internal storage header include (`tl_page.h`)

**ADD:**
- `#include "query/tl_pagespan_iter.h"`
- `PyPageSpan_FromView(tl_pagespan_view_t*, PyObject*)` factory function

**MODIFY:**
- `PyPageSpan` struct - replace `page/row_start/row_end` with `ts/h/len/first_ts/last_ts/timelog`
- Buffer protocol `pagespan_getbuffer()` - use `span->ts` and `span->len`
- Property getters - use cached `first_ts/last_ts` instead of page access
- `PyPageSpan_length()` - use `span->len`
- `pagespan_cleanup()` - call `tl_pagespan_owner_decref` on core owner
- `PyPageSpan_traverse()` - visit `self->timelog`

### 15.3 bindings/cpython/src/py_span_objects.c

**DELETE:**
- Internal storage header include (`tl_page.h`)

**MODIFY:**
- `PyPageSpanObjectsView_length()` - use `span->len`
- `PyPageSpanObjectsView_getitem()` - use `span->h[index]` directly
- `objectsviewiter_next()` - use `span->h[index]` directly
- `PyPageSpanObjectsView_copy()` - use `span->h[index]` directly
- Add NULL check for `span->h` (future-proofing)

### 15.4 bindings/cpython/include/timelogpy/py_span.h

**DELETE:**
- `tl_py_span_owner_t` struct definition
- `tl_py_span_owner_create/incref/decref` declarations
- `PyPageSpan_Create` declaration
- Forward declaration of `tl_page_t`

**ADD:**
- `#include "query/tl_pagespan_iter.h"`
- `PyPageSpan_FromView(tl_pagespan_view_t*, PyObject*)` declaration

**MODIFY:**
- `PyPageSpan` struct - new fields

### 15.5 bindings/cpython/include/timelogpy/py_span_iter.h

**DELETE:**
- `span_desc_t` struct definition
- Documentation about precomputed span arrays

**ADD:**
- Include for `tl_pagespan_iter_t` (via py_span.h)

**MODIFY:**
- `PyPageSpanIter` struct - replace `owner/spans/count/index` with `iter/timelog`
- Documentation to reflect streaming behavior

---

## 16. Test Updates

### 16.1 Internal Field Access Changes

Tests in `test_py_span.c` that access internal fields must be updated:

| Current Access | New Access |
|----------------|------------|
| `ps->row_start` | (removed - use `ps->len`) |
| `ps->row_end` | (removed - use `ps->len`) |
| `ps->row_end - ps->row_start` | `ps->len` |
| `ps->page` | (removed) |
| `ps->owner` (binding's) | `ps->owner` (core's, opaque) |
| `it->spans` | (removed) |
| `it->count` | (removed) |
| `it->index` | (removed) |
| `it->owner` | (removed) |

### 16.2 Specific Test Changes

**`page_spans_with_data` (line ~371-373):**
```c
/* BEFORE */
PyPageSpan* ps = (PyPageSpan*)span;
ASSERT(!ps->closed);
ASSERT(ps->row_end > ps->row_start);

/* AFTER */
PyPageSpan* ps = (PyPageSpan*)span;
ASSERT(!ps->closed);
ASSERT(ps->len > 0);
```

**`span_len` (line ~1339-1340):**
```c
/* BEFORE */
PyPageSpan* ps = (PyPageSpan*)span;
ASSERT_EQ((Py_ssize_t)(ps->row_end - ps->row_start), len);

/* AFTER */
PyPageSpan* ps = (PyPageSpan*)span;
ASSERT_EQ((Py_ssize_t)ps->len, len);
```

**`multiple_spans_share_owner` (line ~1099-1104):**
```c
/* BEFORE */
if (span_count > 1) {
    PyPageSpan* ps0 = (PyPageSpan*)spans[0];
    for (int i = 1; i < span_count; i++) {
        PyPageSpan* ps = (PyPageSpan*)spans[i];
        ASSERT(ps->owner == ps0->owner);
    }
}

/* AFTER - same logic works since PyPageSpan still has owner field */
if (span_count > 1) {
    PyPageSpan* ps0 = (PyPageSpan*)spans[0];
    for (int i = 1; i < span_count; i++) {
        PyPageSpan* ps = (PyPageSpan*)spans[i];
        ASSERT(ps->owner == ps0->owner);  /* Core owner pointer comparison */
    }
}
```

**`iter_exhaustion` (line ~638-639):**
```c
/* BEFORE - checked it->closed */
PyPageSpanIter* it = (PyPageSpanIter*)iter;
ASSERT(it->closed);

/* AFTER - same check still works */
PyPageSpanIter* it = (PyPageSpanIter*)iter;
ASSERT(it->closed);
```

### 16.3 Tests That Should Pass Unchanged

Most tests only use the Python API surface and should pass without modification:
- All buffer protocol tests
- All close semantics tests
- All objects view tests (after internal changes)
- All timestamp correctness tests
- All stress tests

---

## 17. Compatibility and Constraints

- Binding must include `src/query/tl_pagespan_iter.h` (core API header).
- No direct inclusion of `tl_page.h`, `tl_segment.h`, or `tl_manifest.h`.
- The hook must run with the GIL held.
- Refcount operations on `tl_pagespan_owner_t` are not atomic; only use under
  GIL (matches B4 constraints).

---

## 18. Migration Strategy

### 18.1 Phase 1: Header Updates

1. Update `py_span.h`:
   - Remove `tl_py_span_owner_t` definition
   - Add include for `query/tl_pagespan_iter.h`
   - Update `PyPageSpan` struct with new fields
   - Add `PyPageSpan_FromView(tl_pagespan_view_t*, PyObject*)` declaration
   - Add `timelog` field for GC

2. Update `py_span_iter.h`:
   - Remove `span_desc_t` definition
   - Update `PyPageSpanIter` struct
   - Add `timelog` field for GC

### 18.2 Phase 2: py_span_iter.c

1. Add hook context type and release function
2. Replace `PyPageSpanIter_Create`:
   - Remove `collect_spans` call
   - Add hook context allocation
   - Call `tl_pagespan_iter_open`
   - Handle error cleanup
3. Replace `PyPageSpanIter_iternext`:
   - Call `tl_pagespan_iter_next`
   - Call `PyPageSpan_FromView` with `self->timelog`
4. Update `pagespaniter_cleanup`:
   - Call `tl_pagespan_iter_close`
5. Update `PyPageSpanIter_traverse`
6. Delete `collect_spans` and `process_segment_catalog`
7. Remove storage header includes

### 18.3 Phase 3: py_span.c

1. Delete `tl_py_span_owner_*` functions
2. Delete `span_owner_destroy`
3. Delete `PyPageSpan_Create`
4. Add `PyPageSpan_FromView(tl_pagespan_view_t*, PyObject*)`:
   - Transfer view's owner reference
   - Store view pointers and cached values
   - Store timelog reference
5. Update `pagespan_cleanup`:
   - Call `tl_pagespan_owner_decref`
   - Clear timelog ref
6. Update buffer protocol
7. Update property getters
8. Update `PyPageSpan_traverse`
9. Remove storage header include

### 18.4 Phase 4: py_span_objects.c

1. Update to use `span->h` and `span->len`
2. Add NULL check for `span->h`
3. Remove storage header include

### 18.5 Phase 5: Testing

1. Update test field accesses
2. Run full test suite
3. Run with ASan/TSan
4. Verify pins protocol works correctly

---

## 19. Verification Checklist

### Build
- [ ] Compiles with `-Wall -Wextra -Werror`
- [ ] No storage/layout internal headers in binding source files
- [ ] Only `query/tl_pagespan_iter.h` from core

### Behavior Preservation
- [ ] All 36+ existing tests pass
- [ ] Same spans, same order
- [ ] Buffer protocol works (memoryview)
- [ ] Context manager works
- [ ] `pins_exit` called exactly once per iteration session

### Memory Safety
- [ ] ASan clean (no leaks)
- [ ] No UAF on page memory
- [ ] Hook context properly freed
- [ ] Exception state preserved in hook

### Edge Cases
- [ ] Empty timelog -> iter works, returns nothing
- [ ] Empty range (t1 >= t2) -> iter works, returns nothing
- [ ] Invalid kind -> ValueError
- [ ] Closed timelog -> TimelogError
- [ ] close() with exported buffers -> BufferError
- [ ] Multiple close() calls -> idempotent

---

## 20. Summary

This update makes the CPython PageSpan bindings a thin wrapper over the core
pagespan iterator:

- Core owns the algorithm (no duplication in bindings).
- Bindings manage only Python integration: pins, PyObject refs, and buffer
  protocol.
- Data exposure uses the stable `tl_pagespan_view_t` pointers rather than
  direct page layout coupling.

The result is a coherent B4 implementation with minimal churn in the Python
API and maximum reuse of core logic.

---

## Appendix A: Complete New Struct Definitions

### A.1 PyPageSpan

```c
typedef struct {
    PyObject_HEAD
    tl_pagespan_owner_t* owner; /* Core owner (owned ref) */
    PyObject* timelog;          /* Strong ref for GC visibility */
    const tl_ts_t* ts;          /* Pointer to timestamp array */
    const tl_handle_t* h;       /* Pointer to handle array (may be NULL) */
    uint32_t len;               /* Row count */
    tl_ts_t first_ts;           /* Cached first timestamp */
    tl_ts_t last_ts;            /* Cached last timestamp */
    Py_ssize_t shape[1];        /* Buffer protocol shape */
    Py_ssize_t strides[1];      /* Buffer protocol strides */
    uint32_t exports;           /* Active buffer exports */
    uint8_t closed;             /* State flag */
} PyPageSpan;
```

### A.2 PyPageSpanIter

```c
typedef struct {
    PyObject_HEAD
    tl_pagespan_iter_t* iter;   /* Core iterator (owned) */
    PyObject* timelog;          /* Strong ref for GC visibility */
    uint8_t closed;             /* State flag */
} PyPageSpanIter;
```

### A.3 Hook Context

```c
typedef struct tl_py_pagespan_hook_ctx {
    PyObject* timelog;          /* Strong ref, decref on release */
    tl_py_handle_ctx_t* ctx;    /* Borrowed handle context */
    int armed;                  /* 0 until iter_open succeeds */
} tl_py_pagespan_hook_ctx_t;
```
