/**
 * @file py_errors.c
 * @brief Error translation from Timelog status codes to Python exceptions
 */

#include "timelogpy/py_errors.h"

#include <assert.h>
#include <stdarg.h>

static int tlpy_state_has_complete_errors(const tl_py_module_state_t* st)
{
    return st != NULL &&
           st->exc_timelog_error != NULL &&
           st->exc_timelog_busy_error != NULL;
}

static int tlpy_validate_error_pair(PyObject* error, PyObject* busy)
{
    int is_subclass = 0;

    if (!PyExceptionClass_Check(error) || !PyExceptionClass_Check(busy)) {
        PyErr_SetString(PyExc_TypeError,
                        "timelog module errors must be exception classes");
        return -1;
    }

    is_subclass = PyObject_IsSubclass(busy, error);
    if (is_subclass < 0) {
        return -1;
    }
    if (is_subclass == 0) {
        PyErr_SetString(PyExc_TypeError,
                        "timelog module TimelogBusyError must subclass TimelogError");
        return -1;
    }

    return 0;
}

static int tlpy_export_error_pair(PyObject* module, const tl_py_module_state_t* st)
{
    PyObject* module_dict = NULL;

    if (PyModule_AddObjectRef(module, "TimelogError", st->exc_timelog_error) < 0) {
        return -1;
    }
    if (PyModule_AddObjectRef(module, "TimelogBusyError", st->exc_timelog_busy_error) < 0) {
        module_dict = PyModule_GetDict(module);
        if (module_dict != NULL) {
            TL_PY_PRESERVE_EXC_BEGIN;
            if (PyDict_DelItemString(module_dict, "TimelogError") < 0) {
                PyErr_Clear();
            }
            TL_PY_PRESERVE_EXC_END;
        }
        return -1;
    }
    return 0;
}

int TlPy_InitErrors(PyObject* module, tl_py_module_state_t* st)
{
    PyObject* error = NULL;
    PyObject* busy = NULL;

    if (module == NULL || st == NULL) {
        PyErr_SetString(PyExc_RuntimeError,
                        "timelog module state is unavailable");
        return -1;
    }

    if ((st->exc_timelog_error == NULL) != (st->exc_timelog_busy_error == NULL)) {
        PyErr_SetString(PyExc_RuntimeError,
                        "timelog module state has incomplete exception pair");
        TlPy_ClearErrors(st);
        return -1;
    }

    if (tlpy_state_has_complete_errors(st)) {
        return tlpy_export_error_pair(module, st);
    }

    error = PyErr_NewException("timelog._timelog.TimelogError", NULL, NULL);
    if (error == NULL) {
        return -1;
    }

    busy = PyErr_NewException("timelog._timelog.TimelogBusyError", error, NULL);
    if (busy == NULL) {
        Py_DECREF(error);
        return -1;
    }

    if (tlpy_validate_error_pair(error, busy) < 0) {
        Py_DECREF(busy);
        Py_DECREF(error);
        return -1;
    }

    st->exc_timelog_error = error;
    st->exc_timelog_busy_error = busy;

    if (tlpy_export_error_pair(module, st) < 0) {
        TlPy_ClearErrors(st);
        return -1;
    }

    return 0;
}

void TlPy_ClearErrors(tl_py_module_state_t* st)
{
    if (st == NULL) {
        return;
    }

    TL_PY_PRESERVE_EXC_BEGIN;
    Py_CLEAR(st->exc_timelog_busy_error);
    Py_CLEAR(st->exc_timelog_error);
    TL_PY_PRESERVE_EXC_END;
}

int TlPy_ExcContext_InitFromModuleState(tl_py_exc_ctx_t* out,
                                        const tl_py_module_state_t* st)
{
    if (out == NULL) {
        PyErr_SetString(PyExc_RuntimeError,
                        "timelog exception context destination is missing");
        return -1;
    }

    out->timelog_error = NULL;
    out->timelog_busy_error = NULL;

    if (!tlpy_state_has_complete_errors(st)) {
        PyErr_SetString(PyExc_RuntimeError,
                        "timelog module state has no initialized exception pair");
        return -1;
    }

    out->timelog_error = Py_NewRef(st->exc_timelog_error);
    out->timelog_busy_error = Py_NewRef(st->exc_timelog_busy_error);
    return 0;
}

int TlPy_ExcContext_Copy(tl_py_exc_ctx_t* out, const tl_py_exc_ctx_t* src)
{
    if (out == NULL) {
        PyErr_SetString(PyExc_RuntimeError,
                        "timelog exception context destination is missing");
        return -1;
    }

    out->timelog_error = NULL;
    out->timelog_busy_error = NULL;

    if (src == NULL ||
        src->timelog_error == NULL ||
        src->timelog_busy_error == NULL) {
        PyErr_SetString(PyExc_RuntimeError,
                        "timelog exception context is incomplete");
        return -1;
    }

    out->timelog_error = Py_NewRef(src->timelog_error);
    out->timelog_busy_error = Py_NewRef(src->timelog_busy_error);
    return 0;
}

void TlPy_ExcContext_Clear(tl_py_exc_ctx_t* ctx)
{
    if (ctx == NULL) {
        return;
    }

    TL_PY_PRESERVE_EXC_BEGIN;
    Py_CLEAR(ctx->timelog_busy_error);
    Py_CLEAR(ctx->timelog_error);
    TL_PY_PRESERVE_EXC_END;
}

static PyObject* tlpy_status_to_exception_type(const tl_py_exc_ctx_t* ctx,
                                               tl_status_t status)
{
    switch (status) {
        case TL_EINVAL:
            return PyExc_ValueError;
        case TL_ENOMEM:
            return PyExc_MemoryError;
        case TL_EOVERFLOW:
            return PyExc_OverflowError;
        case TL_EINTERNAL:
            return PyExc_SystemError;
        case TL_EBUSY:
            if (ctx != NULL && ctx->timelog_busy_error != NULL) {
                return ctx->timelog_busy_error;
            }
            return PyExc_RuntimeError;
        case TL_ESTATE:
        default:
            if (ctx != NULL && ctx->timelog_error != NULL) {
                return ctx->timelog_error;
            }
            return PyExc_RuntimeError;
    }
}

PyObject* TlPy_RaiseFromExcContext(const tl_py_exc_ctx_t* ctx,
                                   tl_status_t status)
{
#ifndef NDEBUG
    assert(status != TL_OK && status != TL_EOF &&
           "TlPy_RaiseFromExcContext called with success status");
#endif

    PyErr_SetString(tlpy_status_to_exception_type(ctx, status), tl_strerror(status));
    return NULL;
}

PyObject* TlPy_RaiseFromExcContextFmt(const tl_py_exc_ctx_t* ctx,
                                      tl_status_t status,
                                      const char* format, ...)
{
    char buffer[512];
    int n;
    va_list args;

#ifndef NDEBUG
    assert(status != TL_OK && status != TL_EOF &&
           "TlPy_RaiseFromExcContextFmt called with success status");
#endif

    va_start(args, format);
    n = vsnprintf(buffer, sizeof(buffer) - 64, format, args);
    va_end(args);

    if (n >= 0 && (size_t)n < sizeof(buffer) - 64) {
        const char* status_msg = tl_strerror(status);
        size_t remaining = sizeof(buffer) - (size_t)n;
        snprintf(buffer + n, remaining, ": %s", status_msg);
    }

    PyErr_SetString(tlpy_status_to_exception_type(ctx, status), buffer);
    return NULL;
}
