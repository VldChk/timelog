/**
 * @file py_module_state.h
 * @brief Private module-state helpers for timelog._timelog
 */

#ifndef TL_PY_MODULE_STATE_H
#define TL_PY_MODULE_STATE_H

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
    int initialized;
    PyObject* exc_timelog_error;
    PyObject* exc_timelog_busy_error;
    PyObject* type_timelog;
    PyObject* type_timelog_iter;
    PyObject* type_pagespan;
    PyObject* type_pagespan_iter;
    PyObject* type_pagespan_objects_view;
    PyObject* type_pagespan_objects_view_iter;
} tl_py_module_state_t;

/* The project floor is Python 3.12 (pyproject requires-python >= 3.12), so the
 * modern raised-exception API is always available; no pre-3.12 fallback. */
#define TL_PY_PRESERVE_EXC_BEGIN \
    PyObject* tl_py_saved_exc = PyErr_GetRaisedException()
#define TL_PY_PRESERVE_EXC_END \
    PyErr_SetRaisedException(tl_py_saved_exc)

static inline tl_py_module_state_t* TlPy_ModuleState(PyObject* module)
{
    return (tl_py_module_state_t*)PyModule_GetState(module);
}

extern const char TlPy_TimelogModuleName[];
tl_py_module_state_t* TlPy_StateFromType(PyTypeObject* type);
tl_py_module_state_t* TlPy_StateFromObject(PyObject* obj);

/*
 * Define a TlPy<Type>_Check(op, st) predicate: true iff op is non-NULL, st is
 * non-NULL, the type slot has been created, and op is an instance of it. Field
 * is the tl_py_module_state_t member holding the heap type (e.g. type_timelog).
 */
#define TL_PY_DEFINE_CHECK(Fn, Field)                            \
    int Fn(PyObject* op, const tl_py_module_state_t* st)         \
    {                                                            \
        return op != NULL && st != NULL && st->Field != NULL &&  \
               PyObject_TypeCheck(op, (PyTypeObject*)st->Field); \
    }

typedef enum {
    TL_PY_MODULE_FAIL_NONE = 0,
    TL_PY_MODULE_FAIL_AFTER_ERRORS,
    TL_PY_MODULE_FAIL_AFTER_CREATE_TIMELOG,
    TL_PY_MODULE_FAIL_AFTER_CREATE_ITER,
    TL_PY_MODULE_FAIL_AFTER_CREATE_PAGESPAN,
    TL_PY_MODULE_FAIL_AFTER_CREATE_PAGESPAN_ITER,
    TL_PY_MODULE_FAIL_AFTER_CREATE_PAGESPAN_OBJECTS_VIEW,
    TL_PY_MODULE_FAIL_AFTER_CREATE_PAGESPAN_OBJECTS_VIEW_ITER,
    TL_PY_MODULE_FAIL_AFTER_EXPORT_TIMELOG,
    TL_PY_MODULE_FAIL_AFTER_EXPORT_ITER,
    TL_PY_MODULE_FAIL_AFTER_EXPORT_PAGESPAN,
    TL_PY_MODULE_FAIL_AFTER_EXPORT_PAGESPAN_ITER,
    TL_PY_MODULE_FAIL_AFTER_EXPORT_PAGESPAN_OBJECTS_VIEW,
} tl_py_module_failpoint_t;

#ifdef TL_PY_MODULE_TEST_HOOKS
PyObject* TlPy_Test_CreateModule(void);
int TlPy_Test_ExecModule(PyObject* module);
void TlPy_Test_SetExecFailpoint(tl_py_module_failpoint_t failpoint);
int TlPy_Test_ModuleDeclaresPerInterpreterGil(void);
Py_ssize_t TlPy_Test_ModuleStateSize(void);
#endif

#ifdef __cplusplus
}
#endif

#endif /* TL_PY_MODULE_STATE_H */
