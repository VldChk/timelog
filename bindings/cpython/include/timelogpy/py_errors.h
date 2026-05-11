/**
 * @file py_errors.h
 * @brief Error translation from Timelog status codes to Python exceptions
 *
 * Step 3 removes process-global Python exception objects. Extension instances
 * carry explicit exception context copied from their owning module state.
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

typedef struct {
    PyObject* timelog_error;
    PyObject* timelog_busy_error;
} tl_py_exc_ctx_t;

int TlPy_InitErrors(PyObject* module, tl_py_module_state_t* st);
void TlPy_ClearErrors(tl_py_module_state_t* st);

int TlPy_ExcContext_InitFromModuleState(tl_py_exc_ctx_t* out,
                                        const tl_py_module_state_t* st);
int TlPy_ExcContext_Copy(tl_py_exc_ctx_t* out, const tl_py_exc_ctx_t* src);
void TlPy_ExcContext_Clear(tl_py_exc_ctx_t* ctx);

PyObject* TlPy_RaiseFromExcContext(const tl_py_exc_ctx_t* ctx,
                                   tl_status_t status);
PyObject* TlPy_RaiseFromExcContextFmt(const tl_py_exc_ctx_t* ctx,
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
