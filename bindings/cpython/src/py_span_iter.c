/**
 * @file py_span_iter.c
 * @brief PyPageSpanIter CPython extension type implementation (LLD-B4)
 *
 * Implements span collection and iteration over page slices.
 *
 * See: docs/timelog_v1_lld_B4_pagespan_zero_copy.md
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_span_iter.h"
#include "timelogpy/py_span.h"
#include "timelogpy/py_timelog.h"

/* Internal headers for segment/page access */
#include "storage/tl_page.h"
#include "storage/tl_segment.h"
#include "storage/tl_manifest.h"
#include "query/tl_snapshot.h"

/* For tl__malloc/tl__free */
#include "internal/tl_alloc.h"

/*===========================================================================
 * Forward Declarations
 *===========================================================================*/

static void pagespaniter_cleanup(PyPageSpanIter* self);
static int collect_spans(tl_snapshot_t* snap,
                         tl_ts_t t1,
                         tl_ts_t t2,
                         span_desc_t** out_spans,
                         size_t* out_count);

/*===========================================================================
 * Block Direct Construction
 *
 * PageSpanIter is only created via page_spans() factory.
 *===========================================================================*/

static PyObject* PyPageSpanIter_new_error(PyTypeObject* type,
                                           PyObject* args,
                                           PyObject* kwds)
{
    (void)type;
    (void)args;
    (void)kwds;

    PyErr_SetString(PyExc_TypeError,
        "PageSpanIter cannot be instantiated directly; "
        "use Timelog.page_spans()");
    return NULL;
}

/*===========================================================================
 * Factory Function
 *===========================================================================*/

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
        TlPy_RaiseFromStatus(TL_ESTATE);  /* Use consistent error taxonomy */
        return NULL;
    }

    /* CRITICAL: pins_enter BEFORE snapshot_acquire
     * This closes the window where compaction could drain retired handles
     * while we're acquiring the snapshot. See py_handle.h protocol docs.
     */
    tl_py_pins_enter(&tl_obj->handle_ctx);

    /* Acquire snapshot */
    tl_snapshot_t* snap = NULL;
    tl_status_t status = tl_snapshot_acquire(tl_obj->tl, &snap);
    if (status != TL_OK) {
        tl_py_pins_exit_and_maybe_drain(&tl_obj->handle_ctx);
        TlPy_RaiseFromStatus(status);  /* Use consistent error taxonomy */
        return NULL;
    }
    if (!snap) {
        tl_py_pins_exit_and_maybe_drain(&tl_obj->handle_ctx);
        PyErr_SetString(PyExc_RuntimeError, "Snapshot is NULL after acquire");
        return NULL;
    }

    /* Get allocator from snapshot */
    tl_alloc_ctx_t* alloc = tl_snapshot_alloc(snap);
    if (!alloc) {
        tl_snapshot_release(snap);
        tl_py_pins_exit_and_maybe_drain(&tl_obj->handle_ctx);
        PyErr_SetString(PyExc_RuntimeError, "Snapshot allocator is NULL");
        return NULL;
    }

    /* Create shared owner (pins already entered above) */
    tl_py_span_owner_t* owner = tl_py_span_owner_create(timelog, snap, alloc);
    if (!owner) {
        tl_snapshot_release(snap);
        tl_py_pins_exit_and_maybe_drain(&tl_obj->handle_ctx);
        return NULL;
    }

    /* Collect spans from snapshot */
    span_desc_t* spans = NULL;
    size_t count = 0;

    int rc = collect_spans(snap, t1, t2, &spans, &count);
    if (rc < 0) {
        tl_py_span_owner_decref(owner);
        return NULL;
    }

    /* Allocate iterator */
    PyPageSpanIter* self = PyObject_GC_New(PyPageSpanIter, &PyPageSpanIter_Type);
    if (!self) {
        if (spans) tl__free(owner->alloc, spans);
        tl_py_span_owner_decref(owner);
        return NULL;
    }

    self->owner = owner;
    self->spans = spans;
    self->count = count;
    self->index = 0;
    self->closed = 0;

    PyObject_GC_Track((PyObject*)self);
    return (PyObject*)self;
}

/*===========================================================================
 * Span Collection Algorithm
 *
 * Collects all page slices matching [t1, t2) from L1 and L0 segments.
 * Only emits spans from TL_PAGE_FULLY_LIVE pages.
 *
 * Uses binary search via tl_page_catalog_find_first_ge() to skip pages
 * whose max_ts < t1, and tl_page_catalog_find_start_ge() to stop early
 * when all remaining pages start after t2.
 *===========================================================================*/

/**
 * Helper: count and collect spans from a segment catalog using binary search.
 * If spans is NULL, just counts. If non-NULL, collects into spans[*idx].
 */
static void process_segment_catalog(const tl_page_catalog_t* cat,
                                    tl_ts_t t1,
                                    tl_ts_t t2,
                                    span_desc_t* spans,
                                    size_t* idx)
{
    if (!cat || cat->n_pages == 0) return;

    /* Binary search: find first page that might contain records >= t1.
     * This is the first page where max_ts >= t1.
     */
    size_t first = tl_page_catalog_find_first_ge(cat, t1);
    if (first >= cat->n_pages) return;  /* All pages end before t1 */

    /* Binary search: find first page that starts at or after t2.
     * All pages from [first, last) might overlap [t1, t2).
     */
    size_t last = tl_page_catalog_find_start_ge(cat, t2);
    if (last <= first) {
        /* Edge case: check if first page still overlaps
         * (its max_ts >= t1, but need to verify min_ts < t2)
         */
        last = first + 1;
    }

    /* Scan only pages in [first, last) */
    for (size_t p = first; p < last && p < cat->n_pages; p++) {
        const tl_page_meta_t* meta = &cat->pages[p];
        const tl_page_t* page = meta->page;

        if (!page || page->count == 0) continue;

        /* Skip non-live pages (V1 only produces FULLY_LIVE) */
        if (page->flags != TL_PAGE_FULLY_LIVE) continue;

        /* Double-check overlap (should be guaranteed by binary search) */
        if (page->max_ts < t1 || page->min_ts >= t2) continue;

        /* Find row bounds within page */
        size_t row_start = tl_page_lower_bound(page, t1);
        size_t row_end = tl_page_lower_bound(page, t2);

        if (row_start < row_end) {
            if (spans) {
                spans[*idx].page = page;
                spans[*idx].row_start = row_start;
                spans[*idx].row_end = row_end;
            }
            (*idx)++;
        }
    }
}

static int collect_spans(tl_snapshot_t* snap,
                         tl_ts_t t1,
                         tl_ts_t t2,
                         span_desc_t** out_spans,
                         size_t* out_count)
{
    *out_spans = NULL;
    *out_count = 0;

    if (!snap || !snap->manifest) {
        return 0;  /* Empty result is OK */
    }

    const tl_manifest_t* mf = snap->manifest;
    tl_alloc_ctx_t* alloc = tl_snapshot_alloc(snap);

    /* First pass: count spans for allocation */
    size_t total_spans = 0;

    /* Count from L1 segments (using binary search per segment) */
    for (uint32_t s = 0; s < mf->n_l1; s++) {
        const tl_segment_t* seg = mf->l1[s];
        if (!seg || seg->page_count == 0) continue;

        /* Quick segment-level bounds check */
        if (seg->max_ts < t1 || seg->min_ts >= t2) continue;

        process_segment_catalog(&seg->catalog, t1, t2, NULL, &total_spans);
    }

    /* Count from L0 segments (using binary search per segment) */
    for (uint32_t s = 0; s < mf->n_l0; s++) {
        const tl_segment_t* seg = mf->l0[s];
        if (!seg || seg->page_count == 0) continue;

        if (seg->max_ts < t1 || seg->min_ts >= t2) continue;

        process_segment_catalog(&seg->catalog, t1, t2, NULL, &total_spans);
    }

    if (total_spans == 0) {
        return 0;  /* Empty result */
    }

    /* Allocate spans array */
    span_desc_t* spans = tl__malloc(alloc, total_spans * sizeof(span_desc_t));
    if (!spans) {
        PyErr_NoMemory();
        return -1;
    }

    /* Second pass: collect spans */
    size_t idx = 0;

    /* Collect from L1 segments */
    for (uint32_t s = 0; s < mf->n_l1; s++) {
        const tl_segment_t* seg = mf->l1[s];
        if (!seg || seg->page_count == 0) continue;
        if (seg->max_ts < t1 || seg->min_ts >= t2) continue;

        process_segment_catalog(&seg->catalog, t1, t2, spans, &idx);
    }

    /* Collect from L0 segments */
    for (uint32_t s = 0; s < mf->n_l0; s++) {
        const tl_segment_t* seg = mf->l0[s];
        if (!seg || seg->page_count == 0) continue;
        if (seg->max_ts < t1 || seg->min_ts >= t2) continue;

        process_segment_catalog(&seg->catalog, t1, t2, spans, &idx);
    }

    *out_spans = spans;
    *out_count = idx;
    return 0;
}

/*===========================================================================
 * Cleanup (Single Source of Truth)
 *===========================================================================*/

static void pagespaniter_cleanup(PyPageSpanIter* self)
{
    if (self->closed) {
        return;
    }
    self->closed = 1;

    /* Free spans array (using allocator from owner before releasing it) */
    tl_py_span_owner_t* owner = self->owner;
    if (self->spans && owner && owner->alloc) {
        tl__free(owner->alloc, self->spans);
    }
    self->spans = NULL;
    self->count = 0;
    self->index = 0;

    /* Release owner reference */
    self->owner = NULL;

    if (owner) {
        tl_py_span_owner_decref(owner);
    }
}

/*===========================================================================
 * GC Support
 *===========================================================================*/

static int PyPageSpanIter_traverse(PyPageSpanIter* self, visitproc visit, void* arg)
{
    /* Visit the timelog held by our owner.
     * This allows the GC to detect cycles involving PageSpanIter -> owner -> timelog.
     */
    if (self->owner && self->owner->timelog) {
        Py_VISIT(self->owner->timelog);
    }
    return 0;
}

static int PyPageSpanIter_clear(PyPageSpanIter* self)
{
    pagespaniter_cleanup(self);
    return 0;
}

static void PyPageSpanIter_dealloc(PyPageSpanIter* self)
{
    PyObject_GC_UnTrack(self);
    pagespaniter_cleanup(self);
    Py_TYPE(self)->tp_free((PyObject*)self);
}

/*===========================================================================
 * Iterator Protocol
 *===========================================================================*/

static PyObject* PyPageSpanIter_iternext(PyPageSpanIter* self)
{
    if (self->closed || self->index >= self->count) {
        /* Exhausted - cleanup and signal StopIteration */
        if (!self->closed) {
            pagespaniter_cleanup(self);
        }
        return NULL;  /* No exception = StopIteration */
    }

    /* Get current span descriptor (do NOT increment index yet) */
    span_desc_t* desc = &self->spans[self->index];

    /* Create the span object */
    PyObject* span = PyPageSpan_Create(self->owner, desc->page,
                                        desc->row_start, desc->row_end);

    /* Only advance index if creation succeeded.
     * This ensures we don't skip elements on allocation failure.
     */
    if (span) {
        self->index++;
    }

    return span;
}

/*===========================================================================
 * Methods
 *===========================================================================*/

static PyObject* PyPageSpanIter_close(PyPageSpanIter* self, PyObject* noargs)
{
    (void)noargs;
    pagespaniter_cleanup(self);
    Py_RETURN_NONE;
}

static PyObject* PyPageSpanIter_enter(PyPageSpanIter* self, PyObject* noargs)
{
    (void)noargs;
    return Py_NewRef((PyObject*)self);
}

static PyObject* PyPageSpanIter_exit(PyPageSpanIter* self, PyObject* args)
{
    (void)args;
    pagespaniter_cleanup(self);
    Py_RETURN_FALSE;
}

/*===========================================================================
 * Properties
 *===========================================================================*/

static PyObject* PyPageSpanIter_get_closed(PyPageSpanIter* self, void* closure)
{
    (void)closure;
    return PyBool_FromLong(self->closed);
}

/*===========================================================================
 * Method/GetSet Tables
 *===========================================================================*/

static PyMethodDef PyPageSpanIter_methods[] = {
    {"close", (PyCFunction)PyPageSpanIter_close, METH_NOARGS,
     "close() -> None\n\nRelease iterator resources. Idempotent."},
    {"__enter__", (PyCFunction)PyPageSpanIter_enter, METH_NOARGS,
     "Context manager entry."},
    {"__exit__", (PyCFunction)PyPageSpanIter_exit, METH_VARARGS,
     "Context manager exit (closes iterator)."},
    {NULL, NULL, 0, NULL}
};

static PyGetSetDef PyPageSpanIter_getset[] = {
    {"closed", (getter)PyPageSpanIter_get_closed, NULL,
     "True if iterator is closed or exhausted.", NULL},
    {NULL, NULL, NULL, NULL, NULL}
};

/*===========================================================================
 * Type Object
 *===========================================================================*/

PyTypeObject PyPageSpanIter_Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "timelog._timelog.PageSpanIter",
    .tp_doc = PyDoc_STR(
        "Iterator yielding PageSpan objects for a time range.\n\n"
        "Cannot be instantiated directly; use Timelog.page_spans()."
    ),
    .tp_basicsize = sizeof(PyPageSpanIter),
    .tp_itemsize = 0,
    .tp_flags = Py_TPFLAGS_DEFAULT | Py_TPFLAGS_HAVE_GC,
    .tp_new = PyPageSpanIter_new_error,
    .tp_dealloc = (destructor)PyPageSpanIter_dealloc,
    .tp_traverse = (traverseproc)PyPageSpanIter_traverse,
    .tp_clear = (inquiry)PyPageSpanIter_clear,
    .tp_free = PyObject_GC_Del,
    .tp_iter = PyObject_SelfIter,
    .tp_iternext = (iternextfunc)PyPageSpanIter_iternext,
    .tp_methods = PyPageSpanIter_methods,
    .tp_getset = PyPageSpanIter_getset,
};
