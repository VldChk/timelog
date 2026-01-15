/**
 * @file module.c
 * @brief CPython extension module initialization (LLD-B2, B3, B4)
 *
 * This module provides PyInit__timelog() which initializes the timelog._timelog
 * extension module and registers the PyTimelog, PyTimelogIter, and PageSpan types.
 *
 * Module name: timelog._timelog
 *   - Fully qualified name for correct __module__ attributes
 *   - Init function remains PyInit__timelog (last component rule)
 *   - Public Python package imports: from timelog._timelog import Timelog
 *
 * See: docs/timelog_v1_lld_B2_pytimelog_engine_wrapper.md
 *      docs/timelog_v1_lld_B4_pagespan_zero_copy.md
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_timelog.h"
#include "timelogpy/py_iter.h"
#include "timelogpy/py_errors.h"
#include "timelogpy/py_span.h"
#include "timelogpy/py_span_iter.h"
#include "timelogpy/py_span_objects.h"

/*===========================================================================
 * Module Definition
 *
 * No module-level methods - all functionality via PyTimelog type.
 * m_size = -1 means no per-interpreter state (simple global state).
 *===========================================================================*/

static struct PyModuleDef timelog_module = {
    PyModuleDef_HEAD_INIT,
    "timelog._timelog",                   /* m_name */
    "Timelog C extension module.\n\n"     /* m_doc */
    "Provides the Timelog type for time-indexed storage.\n\n"
    "Usage:\n"
    "    from timelog._timelog import Timelog\n"
    "    tl = Timelog()\n"
    "    tl.append(1234567890, my_object)\n"
    "    tl.close()\n\n"
    "See timelog package for the full Python API.",
    -1,                                   /* m_size (no per-module state) */
    NULL,                                 /* m_methods (none at module level) */
    NULL,                                 /* m_slots */
    NULL,                                 /* m_traverse */
    NULL,                                 /* m_clear */
    NULL                                  /* m_free */
};

/*===========================================================================
 * Module Initialization
 *
 * Called by Python when importing _timelog.
 * Order is critical:
 *   1. Create module
 *   2. Initialize error types (they need module for qualified name)
 *   3. Ready the type object
 *   4. Add type to module
 *===========================================================================*/

PyMODINIT_FUNC PyInit__timelog(void)
{
    PyObject* m = NULL;

    /* Create module */
    m = PyModule_Create(&timelog_module);
    if (m == NULL) {
        return NULL;
    }

    /*
     * Initialize error types (TimelogError, TimelogBusyError).
     * Must happen before any error translation can be used.
     * TlPy_InitErrors adds exceptions to the module namespace.
     */
    if (TlPy_InitErrors(m) < 0) {
        goto error;
    }

    /*
     * Ready the PyTimelog type.
     * PyType_Ready fills in tp_dict, tp_bases, etc.
     * Must be called before the type can be used.
     */
    if (PyType_Ready(&PyTimelog_Type) < 0) {
        goto error;
    }

    /*
     * Add PyTimelog type to module.
     * Exposed as timelog._timelog.Timelog in Python.
     *
     * We INCREF because PyModule_AddObject steals a reference only on
     * success. On failure, we need to own the type to DECREF it.
     */
    Py_INCREF(&PyTimelog_Type);
    if (PyModule_AddObject(m, "Timelog", (PyObject*)&PyTimelog_Type) < 0) {
        Py_DECREF(&PyTimelog_Type);
        goto error;
    }

    /*
     * Ready and add PyTimelogIter type (LLD-B3).
     * Exposed as timelog._timelog.TimelogIter in Python.
     *
     * Note: TimelogIter cannot be instantiated directly (tp_new raises TypeError).
     * It is only created via factory methods on Timelog (range, since, etc.).
     */
    if (PyType_Ready(&PyTimelogIter_Type) < 0) {
        goto error;
    }
    Py_INCREF(&PyTimelogIter_Type);
    if (PyModule_AddObject(m, "TimelogIter", (PyObject*)&PyTimelogIter_Type) < 0) {
        Py_DECREF(&PyTimelogIter_Type);
        goto error;
    }

    /*
     * Ready and add PyPageSpan type (LLD-B4).
     * Exposed as timelog._timelog.PageSpan in Python.
     *
     * Note: PageSpan cannot be instantiated directly (tp_new raises TypeError).
     * It is only created via Timelog.page_spans() factory method.
     */
    if (PyType_Ready(&PyPageSpan_Type) < 0) {
        goto error;
    }
    Py_INCREF(&PyPageSpan_Type);
    if (PyModule_AddObject(m, "PageSpan", (PyObject*)&PyPageSpan_Type) < 0) {
        Py_DECREF(&PyPageSpan_Type);
        goto error;
    }

    /*
     * Ready and add PyPageSpanIter type (LLD-B4).
     * Exposed as timelog._timelog.PageSpanIter in Python.
     */
    if (PyType_Ready(&PyPageSpanIter_Type) < 0) {
        goto error;
    }
    Py_INCREF(&PyPageSpanIter_Type);
    if (PyModule_AddObject(m, "PageSpanIter", (PyObject*)&PyPageSpanIter_Type) < 0) {
        Py_DECREF(&PyPageSpanIter_Type);
        goto error;
    }

    /*
     * Ready and add PyPageSpanObjectsView type (LLD-B4).
     * Exposed as timelog._timelog.PageSpanObjectsView in Python.
     */
    if (PyType_Ready(&PyPageSpanObjectsView_Type) < 0) {
        goto error;
    }
    Py_INCREF(&PyPageSpanObjectsView_Type);
    if (PyModule_AddObject(m, "PageSpanObjectsView", (PyObject*)&PyPageSpanObjectsView_Type) < 0) {
        Py_DECREF(&PyPageSpanObjectsView_Type);
        goto error;
    }

    /*
     * Ready PyPageSpanObjectsViewIter type (internal iterator).
     * Not exported to module namespace but must be ready before use.
     * This avoids a race condition in py_span_objects.c.
     */
    if (PyType_Ready(&PyPageSpanObjectsViewIter_Type) < 0) {
        goto error;
    }

    return m;

error:
    Py_XDECREF(m);
    return NULL;
}
