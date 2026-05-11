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

#include <stdint.h>

#include "timelogpy/py_module_state.h"
#include "timelogpy/py_timelog.h"
#include "timelogpy/py_iter.h"
#include "timelogpy/py_errors.h"
#include "timelogpy/py_span.h"
#include "timelogpy/py_span_iter.h"
#include "timelogpy/py_span_objects.h"

static const char module_doc[] =
    "Timelog C extension module.\n\n"
    "Provides the Timelog type for time-indexed storage.\n\n"
    "Usage:\n"
    "    from timelog._timelog import Timelog\n"
    "    tl = Timelog()\n"
    "    tl.append(1234567890, my_object)\n"
    "    tl.close()\n\n"
    "See timelog package for the full Python API.";

const char TlPy_TimelogModuleName[] = "timelog._timelog";

static const char* const managed_export_names[] = {
    "TimelogError",
    "TimelogBusyError",
    "Timelog",
    "TimelogIter",
    "PageSpan",
    "PageSpanIter",
    "PageSpanObjectsView",
};

#ifdef TL_PY_MODULE_TEST_HOOKS
static tl_py_module_failpoint_t tl_py_module_failpoint = TL_PY_MODULE_FAIL_NONE;
#endif

static int timelog_traverse(PyObject* module, visitproc visit, void* arg)
{
    tl_py_module_state_t* st = TlPy_ModuleState(module);

    if (st == NULL) {
        return 0;
    }

    Py_VISIT(st->exc_timelog_error);
    Py_VISIT(st->exc_timelog_busy_error);
    return 0;
}

static int timelog_clear(PyObject* module)
{
    tl_py_module_state_t* st = TlPy_ModuleState(module);

    if (st == NULL) {
        return 0;
    }

    st->initialized = 0;
    TlPy_ClearErrors(st);
    return 0;
}

static void timelog_free(void* module)
{
    (void)module;
}

static void timelog_remove_managed_exports(PyObject* module)
{
    PyObject* module_dict = PyModule_GetDict(module);
    size_t i;

    if (module_dict == NULL) {
        return;
    }

    TL_PY_PRESERVE_EXC_BEGIN;
    for (i = 0; i < sizeof(managed_export_names) / sizeof(managed_export_names[0]); i++) {
        if (PyDict_DelItemString(module_dict, managed_export_names[i]) < 0) {
            PyErr_Clear();
        }
    }
    TL_PY_PRESERVE_EXC_END;
}

#ifdef TL_PY_MODULE_TEST_HOOKS
static int timelog_maybe_fail(tl_py_module_failpoint_t failpoint, const char* stage)
{
    if (tl_py_module_failpoint != failpoint) {
        return 0;
    }

    PyErr_Format(PyExc_RuntimeError, "timelog_exec failpoint at %s", stage);
    return -1;
}
#else
static int timelog_maybe_fail(int failpoint, const char* stage)
{
    (void)failpoint;
    (void)stage;
    return 0;
}
#endif

static int timelog_exec(PyObject* module)
{
    tl_py_module_state_t* st = TlPy_ModuleState(module);

    if (st == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "timelog module state is unavailable");
        return -1;
    }

    if (st->initialized != 0) {
        return 0;
    }

    if (TlPy_InitErrors(module, st) < 0) {
        goto error;
    }

    if (timelog_maybe_fail(TL_PY_MODULE_FAIL_AFTER_ERRORS, "after errors") < 0) {
        goto error;
    }

    if (PyType_Ready(&PyTimelog_Type) < 0) {
        goto error;
    }
    if (PyModule_AddObjectRef(module, "Timelog", (PyObject*)&PyTimelog_Type) < 0) {
        goto error;
    }
    if (timelog_maybe_fail(TL_PY_MODULE_FAIL_AFTER_EXPORT_TIMELOG, "after Timelog export") < 0) {
        goto error;
    }

    if (PyType_Ready(&PyTimelogIter_Type) < 0) {
        goto error;
    }
    if (PyModule_AddObjectRef(module, "TimelogIter", (PyObject*)&PyTimelogIter_Type) < 0) {
        goto error;
    }
    if (timelog_maybe_fail(TL_PY_MODULE_FAIL_AFTER_EXPORT_ITER, "after TimelogIter export") < 0) {
        goto error;
    }

    if (PyType_Ready(&PyPageSpan_Type) < 0) {
        goto error;
    }
    if (PyModule_AddObjectRef(module, "PageSpan", (PyObject*)&PyPageSpan_Type) < 0) {
        goto error;
    }
    if (timelog_maybe_fail(TL_PY_MODULE_FAIL_AFTER_EXPORT_PAGESPAN, "after PageSpan export") < 0) {
        goto error;
    }

    if (PyType_Ready(&PyPageSpanIter_Type) < 0) {
        goto error;
    }
    if (PyModule_AddObjectRef(module, "PageSpanIter", (PyObject*)&PyPageSpanIter_Type) < 0) {
        goto error;
    }
    if (timelog_maybe_fail(TL_PY_MODULE_FAIL_AFTER_EXPORT_PAGESPAN_ITER, "after PageSpanIter export") < 0) {
        goto error;
    }

    if (PyType_Ready(&PyPageSpanObjectsView_Type) < 0) {
        goto error;
    }
    if (PyModule_AddObjectRef(module, "PageSpanObjectsView",
                              (PyObject*)&PyPageSpanObjectsView_Type) < 0) {
        goto error;
    }
    if (timelog_maybe_fail(TL_PY_MODULE_FAIL_AFTER_EXPORT_PAGESPAN_OBJECTS_VIEW,
                           "after PageSpanObjectsView export") < 0) {
        goto error;
    }

    if (PyType_Ready(&PyPageSpanObjectsViewIter_Type) < 0) {
        goto error;
    }
    if (timelog_maybe_fail(TL_PY_MODULE_FAIL_AFTER_INTERNAL_VIEW_ITER_READY,
                           "after PageSpanObjectsViewIter ready") < 0) {
        goto error;
    }

    st->initialized = 1;
    return 0;

error:
    timelog_remove_managed_exports(module);
    st->initialized = 0;
    return -1;
}

static struct PyModuleDef_Slot timelog_slots[] = {
    {Py_mod_exec, timelog_exec},
#if PY_VERSION_HEX >= 0x030C0000
    {Py_mod_multiple_interpreters, Py_MOD_MULTIPLE_INTERPRETERS_NOT_SUPPORTED},
#endif
    {0, NULL},
};

static struct PyModuleDef timelog_module = {
    PyModuleDef_HEAD_INIT,
    TlPy_TimelogModuleName,              /* m_name */
    module_doc,                           /* m_doc */
    sizeof(tl_py_module_state_t),         /* m_size */
    NULL,                                 /* m_methods */
    timelog_slots,                        /* m_slots */
    timelog_traverse,                     /* m_traverse */
    timelog_clear,                        /* m_clear */
    timelog_free                          /* m_free */
};

PyMODINIT_FUNC PyInit__timelog(void)
{
    return PyModuleDef_Init(&timelog_module);
}

int TlPy_ModuleMatchesTimelogDef(PyObject* module)
{
    return module != NULL && PyModule_GetDef(module) == &timelog_module;
}

#ifdef TL_PY_MODULE_TEST_HOOKS
static PyObject* timelog_test_build_spec(void)
{
    PyObject* importlib_util = PyImport_ImportModule("importlib.util");
    PyObject* spec_from_loader = NULL;
    PyObject* name = NULL;
    PyObject* spec = NULL;

    if (importlib_util == NULL) {
        return NULL;
    }

    spec_from_loader = PyObject_GetAttrString(importlib_util, "spec_from_loader");
    Py_DECREF(importlib_util);
    if (spec_from_loader == NULL) {
        return NULL;
    }

    name = PyUnicode_FromString(TlPy_TimelogModuleName);
    if (name == NULL) {
        Py_DECREF(spec_from_loader);
        return NULL;
    }

    spec = PyObject_CallFunctionObjArgs(spec_from_loader, name, Py_None, NULL);
    Py_DECREF(spec_from_loader);
    Py_DECREF(name);
    return spec;
}

PyObject* TlPy_Test_CreateModule(void)
{
    PyObject* spec = timelog_test_build_spec();
    PyObject* module;

    if (spec == NULL) {
        return NULL;
    }

    module = PyModule_FromDefAndSpec(&timelog_module, spec);
    Py_DECREF(spec);
    return module;
}

int TlPy_Test_ExecModule(PyObject* module)
{
    return PyModule_ExecDef(module, &timelog_module);
}

void TlPy_Test_SetExecFailpoint(tl_py_module_failpoint_t failpoint)
{
    tl_py_module_failpoint = failpoint;
}

int TlPy_Test_ModuleDeclaresNoSubinterpreters(void)
{
    PyModuleDef_Slot* slot = timelog_slots;

    while (slot->slot != 0) {
        if (slot->slot == Py_mod_multiple_interpreters) {
            return (intptr_t)slot->value ==
                   (intptr_t)Py_MOD_MULTIPLE_INTERPRETERS_NOT_SUPPORTED;
        }
        slot++;
    }
    return 0;
}

Py_ssize_t TlPy_Test_ModuleStateSize(void)
{
    return timelog_module.m_size;
}
#endif
