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
 *   - Public Python package imports: from timelog import Timelog
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include <stdint.h>
#include <string.h>

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
    "    from timelog import Timelog\n"
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

#define TIMELOG_MANAGED_EXPORT_COUNT \
    (sizeof(managed_export_names) / sizeof(managed_export_names[0]))

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
    Py_VISIT(st->type_timelog);
    Py_VISIT(st->type_timelog_iter);
    Py_VISIT(st->type_pagespan);
    Py_VISIT(st->type_pagespan_iter);
    Py_VISIT(st->type_pagespan_objects_view);
    Py_VISIT(st->type_pagespan_objects_view_iter);
    return 0;
}

static void timelog_clear_types(tl_py_module_state_t* st)
{
    if (st == NULL) {
        return;
    }

    TL_PY_PRESERVE_EXC_BEGIN;
    Py_CLEAR(st->type_pagespan_objects_view_iter);
    Py_CLEAR(st->type_pagespan_objects_view);
    Py_CLEAR(st->type_pagespan_iter);
    Py_CLEAR(st->type_pagespan);
    Py_CLEAR(st->type_timelog_iter);
    Py_CLEAR(st->type_timelog);
    TL_PY_PRESERVE_EXC_END;
}

static void timelog_clear_state_refs(tl_py_module_state_t* st)
{
    if (st == NULL) {
        return;
    }

    timelog_clear_types(st);
    TlPy_ClearErrors(st);
}

static int timelog_clear(PyObject* module)
{
    tl_py_module_state_t* st = TlPy_ModuleState(module);

    if (st == NULL) {
        return 0;
    }

    st->initialized = 0;
    timelog_clear_state_refs(st);
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

static int timelog_state_has_empty_errors(const tl_py_module_state_t* st)
{
    return st != NULL &&
           st->exc_timelog_error == NULL &&
           st->exc_timelog_busy_error == NULL;
}

static int timelog_state_has_empty_types(const tl_py_module_state_t* st)
{
    return st != NULL &&
           st->type_timelog == NULL &&
           st->type_timelog_iter == NULL &&
           st->type_pagespan == NULL &&
           st->type_pagespan_iter == NULL &&
           st->type_pagespan_objects_view == NULL &&
           st->type_pagespan_objects_view_iter == NULL;
}

static int timelog_state_has_complete_types(const tl_py_module_state_t* st)
{
    return st != NULL &&
           st->type_timelog != NULL &&
           st->type_timelog_iter != NULL &&
           st->type_pagespan != NULL &&
           st->type_pagespan_iter != NULL &&
           st->type_pagespan_objects_view != NULL &&
           st->type_pagespan_objects_view_iter != NULL;
}

static int timelog_state_is_invalid(const tl_py_module_state_t* st)
{
    int errors_empty;
    int errors_complete;
    int types_empty;
    int types_complete;

    if (st == NULL) {
        return 1;
    }

    errors_empty = timelog_state_has_empty_errors(st);
    errors_complete = TlPy_StateHasCompleteErrors(st);
    types_empty = timelog_state_has_empty_types(st);
    types_complete = timelog_state_has_complete_types(st);

    if (!errors_empty && !errors_complete) {
        return 1;
    }
    if (!types_empty && !types_complete) {
        return 1;
    }
    if (types_complete && !errors_complete) {
        return 1;
    }
    if (st->initialized != 0 && (!errors_complete || !types_complete)) {
        return 1;
    }
    return 0;
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

typedef struct {
    const char* name;
    PyObject* value;
    tl_py_module_failpoint_t failpoint;
    const char* stage;
} timelog_export_entry_t;

typedef struct {
    PyObject* old_value;
    int existed;
} timelog_export_snapshot_t;

static int timelog_snapshot_exports(PyObject* module,
                                    timelog_export_snapshot_t* snapshots,
                                    size_t n)
{
    PyObject* module_dict = PyModule_GetDict(module);
    size_t i;

    if (module_dict == NULL) {
        return -1;
    }

    for (i = 0; i < n; i++) {
        PyObject* old = PyDict_GetItemString(module_dict, managed_export_names[i]);
        snapshots[i].old_value = old != NULL ? Py_NewRef(old) : NULL;
        snapshots[i].existed = old != NULL;
    }
    return 0;
}

static void timelog_discard_export_snapshots(timelog_export_snapshot_t* snapshots,
                                             size_t n)
{
    size_t i;
    for (i = 0; i < n; i++) {
        Py_XDECREF(snapshots[i].old_value);
        snapshots[i].old_value = NULL;
        snapshots[i].existed = 0;
    }
}

static void timelog_restore_exports(PyObject* module,
                                    timelog_export_snapshot_t* snapshots,
                                    size_t n)
{
    PyObject* module_dict = PyModule_GetDict(module);
    size_t i;

    if (module_dict == NULL) {
        timelog_discard_export_snapshots(snapshots, n);
        return;
    }

    TL_PY_PRESERVE_EXC_BEGIN;
    for (i = 0; i < n; i++) {
        if (snapshots[i].existed) {
            if (PyDict_SetItemString(module_dict, managed_export_names[i],
                                     snapshots[i].old_value) < 0) {
                PyErr_Clear();
            }
        } else {
            if (PyDict_DelItemString(module_dict, managed_export_names[i]) < 0) {
                PyErr_Clear();
            }
        }
    }
    TL_PY_PRESERVE_EXC_END;
    timelog_discard_export_snapshots(snapshots, n);
}

static int timelog_export_public_refs(PyObject* module, tl_py_module_state_t* st)
{
    timelog_export_entry_t entries[] = {
        {"TimelogError", st->exc_timelog_error, TL_PY_MODULE_FAIL_NONE, NULL},
        {"TimelogBusyError", st->exc_timelog_busy_error, TL_PY_MODULE_FAIL_NONE, NULL},
        {"Timelog", st->type_timelog, TL_PY_MODULE_FAIL_AFTER_EXPORT_TIMELOG,
         "after Timelog export"},
        {"TimelogIter", st->type_timelog_iter, TL_PY_MODULE_FAIL_AFTER_EXPORT_ITER,
         "after TimelogIter export"},
        {"PageSpan", st->type_pagespan, TL_PY_MODULE_FAIL_AFTER_EXPORT_PAGESPAN,
         "after PageSpan export"},
        {"PageSpanIter", st->type_pagespan_iter, TL_PY_MODULE_FAIL_AFTER_EXPORT_PAGESPAN_ITER,
         "after PageSpanIter export"},
        {"PageSpanObjectsView", st->type_pagespan_objects_view,
         TL_PY_MODULE_FAIL_AFTER_EXPORT_PAGESPAN_OBJECTS_VIEW,
        "after PageSpanObjectsView export"},
    };
    _Static_assert(sizeof(entries) / sizeof(entries[0]) ==
                   TIMELOG_MANAGED_EXPORT_COUNT,
                   "managed_export_names and entries must stay in lockstep");
    timelog_export_snapshot_t snapshots[
        TIMELOG_MANAGED_EXPORT_COUNT
    ];
    size_t i;

    memset(snapshots, 0, sizeof(snapshots));

    if (timelog_snapshot_exports(module, snapshots,
                                 sizeof(snapshots) / sizeof(snapshots[0])) < 0) {
        return -1;
    }

    for (i = 0; i < sizeof(entries) / sizeof(entries[0]); i++) {
        if (PyModule_AddObjectRef(module, entries[i].name, entries[i].value) < 0) {
            goto error;
        }
        if (entries[i].failpoint != TL_PY_MODULE_FAIL_NONE &&
            timelog_maybe_fail(entries[i].failpoint, entries[i].stage) < 0) {
            goto error;
        }
    }

    timelog_discard_export_snapshots(snapshots,
                                     sizeof(snapshots) / sizeof(snapshots[0]));
    return 0;

error:
    timelog_restore_exports(module, snapshots,
                            sizeof(snapshots) / sizeof(snapshots[0]));
    return -1;
}

static int timelog_create_types(PyObject* module, tl_py_module_state_t* st)
{
    if (timelog_state_has_complete_types(st)) {
        return 0;
    }

    if (!timelog_state_has_empty_types(st)) {
        PyErr_SetString(PyExc_RuntimeError,
                        "timelog module state has incomplete type set");
        timelog_clear_types(st);
        return -1;
    }

    st->type_timelog = TlPy_CreateTimelogType(module);
    if (st->type_timelog == NULL ||
        timelog_maybe_fail(TL_PY_MODULE_FAIL_AFTER_CREATE_TIMELOG,
                           "after Timelog type creation") < 0) {
        goto error;
    }

    st->type_timelog_iter = TlPy_CreateTimelogIterType(module);
    if (st->type_timelog_iter == NULL ||
        timelog_maybe_fail(TL_PY_MODULE_FAIL_AFTER_CREATE_ITER,
                           "after TimelogIter type creation") < 0) {
        goto error;
    }

    st->type_pagespan = TlPy_CreatePageSpanType(module);
    if (st->type_pagespan == NULL ||
        timelog_maybe_fail(TL_PY_MODULE_FAIL_AFTER_CREATE_PAGESPAN,
                           "after PageSpan type creation") < 0) {
        goto error;
    }

    st->type_pagespan_iter = TlPy_CreatePageSpanIterType(module);
    if (st->type_pagespan_iter == NULL ||
        timelog_maybe_fail(TL_PY_MODULE_FAIL_AFTER_CREATE_PAGESPAN_ITER,
                           "after PageSpanIter type creation") < 0) {
        goto error;
    }

    st->type_pagespan_objects_view = TlPy_CreatePageSpanObjectsViewType(module);
    if (st->type_pagespan_objects_view == NULL ||
        timelog_maybe_fail(TL_PY_MODULE_FAIL_AFTER_CREATE_PAGESPAN_OBJECTS_VIEW,
                           "after PageSpanObjectsView type creation") < 0) {
        goto error;
    }

    st->type_pagespan_objects_view_iter = TlPy_CreatePageSpanObjectsViewIterType(module);
    if (st->type_pagespan_objects_view_iter == NULL ||
        timelog_maybe_fail(TL_PY_MODULE_FAIL_AFTER_CREATE_PAGESPAN_OBJECTS_VIEW_ITER,
                           "after PageSpanObjectsViewIter type creation") < 0) {
        goto error;
    }
    return 0;

error:
    timelog_clear_types(st);
    return -1;
}

static int timelog_exec(PyObject* module)
{
    tl_py_module_state_t* st = TlPy_ModuleState(module);

    if (st == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "timelog module state is unavailable");
        return -1;
    }

    if (timelog_state_is_invalid(st)) {
        timelog_remove_managed_exports(module);
        timelog_clear_state_refs(st);
        st->initialized = 0;
        PyErr_SetString(PyExc_RuntimeError,
                        "timelog module state is partially initialized");
        return -1;
    }

    if (TlPy_StateHasCompleteErrors(st) &&
        timelog_state_has_complete_types(st)) {
        if (timelog_export_public_refs(module, st) < 0) {
            st->initialized = 0;
            return -1;
        }
        st->initialized = 1;
        return 0;
    }

    if (TlPy_InitErrors(module, st) < 0) {
        goto error;
    }

    if (timelog_maybe_fail(TL_PY_MODULE_FAIL_AFTER_ERRORS, "after errors") < 0) {
        goto error;
    }

    if (timelog_create_types(module, st) < 0) {
        goto error;
    }

    if (timelog_export_public_refs(module, st) < 0) {
        st->initialized = 0;
        return -1;
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
    {Py_mod_multiple_interpreters, Py_MOD_PER_INTERPRETER_GIL_SUPPORTED},
#endif
#if PY_VERSION_HEX >= 0x030D0000
    /* Safe to run without the GIL on free-threaded CPython 3.13+: every
     * mutable structure has its own explicit synchronization (per-instance
     * core lock, per-context live-table lock, per-object critical sections,
     * atomic refcounts and a lock-free retired-handle stack), and the core
     * maintenance thread never touches the Python C-API. */
    {Py_mod_gil, Py_MOD_GIL_NOT_USED},
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

tl_py_module_state_t* TlPy_StateFromType(PyTypeObject* type)
{
    PyObject* module = NULL;
    tl_py_module_state_t* st = NULL;

    if (type == NULL) {
        PyErr_SetString(PyExc_RuntimeError,
                        "timelog module state is unavailable");
        return NULL;
    }

    module = PyType_GetModuleByDef(type, &timelog_module);
    if (module == NULL) {
        if (!PyErr_Occurred()) {
            PyErr_SetString(PyExc_RuntimeError,
                            "timelog module state is unavailable");
        }
        return NULL;
    }

    st = TlPy_ModuleState(module);
    if (st == NULL ||
        !TlPy_StateHasCompleteErrors(st) ||
        !timelog_state_has_complete_types(st)) {
        PyErr_SetString(PyExc_RuntimeError,
                        "timelog module state is unavailable");
        return NULL;
    }
    return st;
}

tl_py_module_state_t* TlPy_StateFromObject(PyObject* obj)
{
    if (obj == NULL) {
        PyErr_SetString(PyExc_RuntimeError,
                        "timelog module state is unavailable");
        return NULL;
    }
    return TlPy_StateFromType(Py_TYPE(obj));
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

int TlPy_Test_ModuleDeclaresPerInterpreterGil(void)
{
    PyModuleDef_Slot* slot = timelog_slots;

    while (slot->slot != 0) {
        if (slot->slot == Py_mod_multiple_interpreters) {
            return (intptr_t)slot->value ==
                   (intptr_t)Py_MOD_PER_INTERPRETER_GIL_SUPPORTED;
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
