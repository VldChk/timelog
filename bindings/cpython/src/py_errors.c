/**
 * @file py_errors.c
 * @brief Error translation from Timelog status codes to Python exceptions
 */

#include "timelogpy/py_errors.h"

#include <assert.h>
#include <stdarg.h>

/*===========================================================================
 * Exception Types
 *===========================================================================*/

PyObject* TlPy_TimelogError = NULL;
PyObject* TlPy_TimelogBusyError = NULL;

/*===========================================================================
 * Module Initialization
 *===========================================================================*/

int TlPy_InitErrors(PyObject* module)
{
    /* Qualified name matches installed module path (timelog/_timelog). */
    TlPy_TimelogError = PyErr_NewException(
        "timelog._timelog.TimelogError",  /* name (installed path: timelog/_timelog) */
        NULL,                              /* base (Exception) */
        NULL                               /* dict */
    );

    if (TlPy_TimelogError == NULL) {
        return -1;
    }

    if (PyModule_AddObject(module, "TimelogError", TlPy_TimelogError) < 0) {
        Py_DECREF(TlPy_TimelogError);
        TlPy_TimelogError = NULL;
        return -1;
    }

    /* PyModule_AddObject steals ref on success; keep our own. */
    Py_INCREF(TlPy_TimelogError);

    /* TimelogBusyError: subclass for TL_EBUSY conditions. */
    TlPy_TimelogBusyError = PyErr_NewException(
        "timelog._timelog.TimelogBusyError",  /* name */
        TlPy_TimelogError,                     /* base (TimelogError) */
        NULL                                   /* dict */
    );

    if (TlPy_TimelogBusyError == NULL) {
        Py_DECREF(TlPy_TimelogError);
        TlPy_TimelogError = NULL;
        return -1;
    }

    if (PyModule_AddObject(module, "TimelogBusyError", TlPy_TimelogBusyError) < 0) {
        Py_DECREF(TlPy_TimelogBusyError);
        TlPy_TimelogBusyError = NULL;
        Py_DECREF(TlPy_TimelogError);
        TlPy_TimelogError = NULL;
        return -1;
    }

    Py_INCREF(TlPy_TimelogBusyError);

    return 0;
}

void TlPy_FiniErrors(void)
{
    Py_CLEAR(TlPy_TimelogBusyError);
    Py_CLEAR(TlPy_TimelogError);
}

/*===========================================================================
 * Error Translation
 *===========================================================================*/

/** Map tl_status_t to Python exception type (see py_errors.h for mapping). */
static PyObject* status_to_exception_type(tl_status_t status)
{
    switch (status) {
        case TL_EINVAL:
            return PyExc_ValueError;

        case TL_EBUSY:
            return TlPy_TimelogBusyError ? TlPy_TimelogBusyError
                                          : PyExc_RuntimeError;

        case TL_ENOMEM:
            return PyExc_MemoryError;

        case TL_EOVERFLOW:
            return PyExc_OverflowError;

        case TL_EINTERNAL:
            return PyExc_SystemError;

        case TL_ESTATE:
        default:
            return TlPy_TimelogError ? TlPy_TimelogError : PyExc_RuntimeError;
    }
}

PyObject* TlPy_RaiseFromStatus(tl_status_t status)
{
#ifndef NDEBUG
    assert(status != TL_OK && status != TL_EOF &&
           "TlPy_RaiseFromStatus called with success status");
#endif

    PyObject* exc_type = status_to_exception_type(status);
    const char* msg = tl_strerror(status);

    PyErr_SetString(exc_type, msg);
    return NULL;
}

PyObject* TlPy_RaiseFromStatusFmt(tl_status_t status,
                                   const char* format, ...)
{
#ifndef NDEBUG
    assert(status != TL_OK && status != TL_EOF &&
           "TlPy_RaiseFromStatusFmt called with success status");
#endif

    PyObject* exc_type = status_to_exception_type(status);

    va_list args;
    va_start(args, format);

    /* Format: "user message: tl_strerror(status)" */
    char buffer[512];
    int n = vsnprintf(buffer, sizeof(buffer) - 64, format, args);
    va_end(args);

    /* Append status string if there's room (truncation is harmless). */
    if (n >= 0 && (size_t)n < sizeof(buffer) - 64) {
        const char* status_msg = tl_strerror(status);
        size_t remaining = sizeof(buffer) - (size_t)n;
        snprintf(buffer + n, remaining, ": %s", status_msg);
    }

    PyErr_SetString(exc_type, buffer);
    return NULL;
}
