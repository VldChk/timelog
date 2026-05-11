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
} tl_py_module_state_t;

#if PY_VERSION_HEX >= 0x030C0000
#define TL_PY_PRESERVE_EXC_BEGIN \
    PyObject* tl_py_saved_exc = PyErr_GetRaisedException()
#define TL_PY_PRESERVE_EXC_END \
    PyErr_SetRaisedException(tl_py_saved_exc)
#else
#define TL_PY_PRESERVE_EXC_BEGIN \
    PyObject *exc_type = NULL, *exc_value = NULL, *exc_tb = NULL; \
    PyErr_Fetch(&exc_type, &exc_value, &exc_tb)
#define TL_PY_PRESERVE_EXC_END \
    PyErr_Restore(exc_type, exc_value, exc_tb)
#endif

static inline tl_py_module_state_t* TlPy_ModuleState(PyObject* module)
{
    return (tl_py_module_state_t*)PyModule_GetState(module);
}

extern const char TlPy_TimelogModuleName[];
int TlPy_ModuleMatchesTimelogDef(PyObject* module);

typedef enum {
    TL_PY_MODULE_FAIL_NONE = 0,
    TL_PY_MODULE_FAIL_AFTER_ERRORS,
    TL_PY_MODULE_FAIL_AFTER_EXPORT_TIMELOG,
    TL_PY_MODULE_FAIL_AFTER_EXPORT_ITER,
    TL_PY_MODULE_FAIL_AFTER_EXPORT_PAGESPAN,
    TL_PY_MODULE_FAIL_AFTER_EXPORT_PAGESPAN_ITER,
    TL_PY_MODULE_FAIL_AFTER_EXPORT_PAGESPAN_OBJECTS_VIEW,
    TL_PY_MODULE_FAIL_AFTER_INTERNAL_VIEW_ITER_READY,
} tl_py_module_failpoint_t;

#ifdef TL_PY_MODULE_TEST_HOOKS
PyObject* TlPy_Test_CreateModule(void);
int TlPy_Test_ExecModule(PyObject* module);
void TlPy_Test_SetExecFailpoint(tl_py_module_failpoint_t failpoint);
int TlPy_Test_ModuleDeclaresNoSubinterpreters(void);
Py_ssize_t TlPy_Test_ModuleStateSize(void);
#endif

#ifdef __cplusplus
}
#endif

#endif /* TL_PY_MODULE_STATE_H */
