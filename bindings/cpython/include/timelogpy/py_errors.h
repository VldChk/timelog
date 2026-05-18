/**
 * @file py_errors.h
 * @brief Error translation from Timelog status codes to Python exceptions
 *
 * Exception objects live in module state. Runtime code recovers the defining
 * module state from heap types when translating core status codes.
 */

#ifndef TL_PY_ERRORS_H
#define TL_PY_ERRORS_H

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelog/timelog.h"
#include "timelogpy/py_module_state.h"

#ifdef __cplusplus
extern "C" {
#endif

int TlPy_InitErrors(PyObject* module, tl_py_module_state_t* st);
void TlPy_ClearErrors(tl_py_module_state_t* st);
int TlPy_StateHasCompleteErrors(const tl_py_module_state_t* st);

PyObject* TlPy_RaiseFromState(const tl_py_module_state_t* st,
                              tl_status_t status);
PyObject* TlPy_RaiseFromStateFmt(const tl_py_module_state_t* st,
                                 tl_status_t status,
                                 const char* format, ...);
PyObject* TlPy_RaiseFromObject(PyObject* obj, tl_status_t status);
PyObject* TlPy_RaiseFromObjectFmt(PyObject* obj,
                                  tl_status_t status,
                                  const char* format, ...);

static inline int TlPy_StatusOK(tl_status_t status)
{
    return status == TL_OK || status == TL_EOF;
}

#ifdef __cplusplus
}
#endif

#endif /* TL_PY_ERRORS_H */
