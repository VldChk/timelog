/**
 * @file py_errors.c
 * @brief Error translation from Timelog status codes to Python exceptions
 */

#include "timelogpy/py_errors.h"

#include <assert.h>
#include <stdarg.h>

int TlPy_StateHasCompleteErrors(const tl_py_module_state_t* st)
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

    if (TlPy_StateHasCompleteErrors(st)) {
        return tlpy_validate_error_pair(st->exc_timelog_error,
                                        st->exc_timelog_busy_error);
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

static PyObject* tlpy_status_to_exception_type(const tl_py_module_state_t* st,
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
            if (st != NULL && st->exc_timelog_busy_error != NULL) {
                return st->exc_timelog_busy_error;
            }
            return PyExc_RuntimeError;
        case TL_ESTATE:
        default:
            if (st != NULL && st->exc_timelog_error != NULL) {
                return st->exc_timelog_error;
            }
            return PyExc_RuntimeError;
    }
}

PyObject* TlPy_RaiseFromState(const tl_py_module_state_t* st,
                              tl_status_t status)
{
#ifndef NDEBUG
    assert(status != TL_OK && status != TL_EOF &&
           "TlPy_RaiseFromState called with success status");
#endif

    PyErr_SetString(tlpy_status_to_exception_type(st, status), tl_strerror(status));
    return NULL;
}

PyObject* TlPy_RaiseFromStateFmt(const tl_py_module_state_t* st,
                                 tl_status_t status,
                                 const char* format, ...)
{
    char buffer[512];
    int n;
    va_list args;

#ifndef NDEBUG
    assert(status != TL_OK && status != TL_EOF &&
           "TlPy_RaiseFromStateFmt called with success status");
#endif

    va_start(args, format);
    n = vsnprintf(buffer, sizeof(buffer), format, args);
    va_end(args);

    /* The formatted message stands alone. The engine status is already
     * encoded in the exception TYPE; appending ": invalid state" /
     * ": resource busy" to a complete sentence read like a formatting bug
     * (v1.3 usability lab, multiple personas). An empty message falls back
     * to the status text so the exception is never blank. */
    if (n <= 0 || buffer[0] == '\0') {
        snprintf(buffer, sizeof(buffer), "%s", tl_strerror(status));
    }
    PyErr_SetString(tlpy_status_to_exception_type(st, status), buffer);
    return NULL;
}

PyObject* TlPy_RaiseFromObject(PyObject* obj, tl_status_t status)
{
    tl_py_module_state_t* st = TlPy_StateFromObject(obj);
    if (st == NULL) {
        return NULL;
    }
    return TlPy_RaiseFromState(st, status);
}

PyObject* TlPy_RaiseFromObjectFmt(PyObject* obj,
                                  tl_status_t status,
                                  const char* format, ...)
{
    tl_py_module_state_t* st = TlPy_StateFromObject(obj);
    char buffer[512];
    int n;
    va_list args;

#ifndef NDEBUG
    assert(status != TL_OK && status != TL_EOF &&
           "TlPy_RaiseFromObjectFmt called with success status");
#endif

    if (st == NULL) {
        return NULL;
    }

    va_start(args, format);
    n = vsnprintf(buffer, sizeof(buffer), format, args);
    va_end(args);

    /* See TlPy_RaiseFromStateFmt: no status-name suffix on custom messages;
     * empty messages fall back to the status text. */
    if (n <= 0 || buffer[0] == '\0') {
        snprintf(buffer, sizeof(buffer), "%s", tl_strerror(status));
    }
    PyErr_SetString(tlpy_status_to_exception_type(st, status), buffer);
    return NULL;
}
