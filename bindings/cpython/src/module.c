/**
 * @file module.c
 * @brief CPython extension module initialization
 *
 * This module provides PyInit__timelog() which initializes the timelog._timelog
 * extension module and registers the PyTimelog, PyTimelogIter, and PageSpan types.
 *
 * Module name: timelog._timelog
 *   - Fully qualified name for correct __module__ attributes
 *   - Init function remains PyInit__timelog (last component rule)
 *   - Public Python package imports: from timelog._timelog import Timelog
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
    int errors_inited = 0;

    /* Create module */
    m = PyModule_Create(&timelog_module);
    if (m == NULL) {
        return NULL;
    }

    /* Initialize exception types (must precede error translation). */
    if (TlPy_InitErrors(m) < 0) {
        goto error;
    }
    errors_inited = 1;

    /* Ready and add PyTimelog type. */
    if (PyType_Ready(&PyTimelog_Type) < 0) {
        goto error;
    }

    /* INCREF: PyModule_AddObject steals ref only on success. */
    Py_INCREF(&PyTimelog_Type);
    if (PyModule_AddObject(m, "Timelog", (PyObject*)&PyTimelog_Type) < 0) {
        Py_DECREF(&PyTimelog_Type);
        goto error;
    }

    /* Ready and add PyTimelogIter (factory-only, no direct construction). */
    if (PyType_Ready(&PyTimelogIter_Type) < 0) {
        goto error;
    }
    Py_INCREF(&PyTimelogIter_Type);
    if (PyModule_AddObject(m, "TimelogIter", (PyObject*)&PyTimelogIter_Type) < 0) {
        Py_DECREF(&PyTimelogIter_Type);
        goto error;
    }

    /* Ready and add PyPageSpan (factory-only). */
    if (PyType_Ready(&PyPageSpan_Type) < 0) {
        goto error;
    }
    Py_INCREF(&PyPageSpan_Type);
    if (PyModule_AddObject(m, "PageSpan", (PyObject*)&PyPageSpan_Type) < 0) {
        Py_DECREF(&PyPageSpan_Type);
        goto error;
    }

    /* Ready and add PyPageSpanIter. */
    if (PyType_Ready(&PyPageSpanIter_Type) < 0) {
        goto error;
    }
    Py_INCREF(&PyPageSpanIter_Type);
    if (PyModule_AddObject(m, "PageSpanIter", (PyObject*)&PyPageSpanIter_Type) < 0) {
        Py_DECREF(&PyPageSpanIter_Type);
        goto error;
    }

    /* Ready and add PyPageSpanObjectsView. */
    if (PyType_Ready(&PyPageSpanObjectsView_Type) < 0) {
        goto error;
    }
    Py_INCREF(&PyPageSpanObjectsView_Type);
    if (PyModule_AddObject(m, "PageSpanObjectsView", (PyObject*)&PyPageSpanObjectsView_Type) < 0) {
        Py_DECREF(&PyPageSpanObjectsView_Type);
        goto error;
    }

    /* Internal iterator type; not exported but must be readied. */
    if (PyType_Ready(&PyPageSpanObjectsViewIter_Type) < 0) {
        goto error;
    }

    return m;

error:
    if (errors_inited) {
        TlPy_FiniErrors();
    }
    Py_XDECREF(m);
    return NULL;
}
