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

/**
 * Base TimelogError exception.
 * All Timelog-specific errors inherit from this.
 */
PyObject* TlPy_TimelogError = NULL;

/**
 * TimelogBusyError exception for TL_EBUSY.
 * Inherits from TimelogError. Indicates a transient condition.
 */
PyObject* TlPy_TimelogBusyError = NULL;

/*===========================================================================
 * Module Initialization
 *===========================================================================*/

int TlPy_InitErrors(PyObject* module)
{
    /*
     * Create TimelogError exception type.
     *
     * The qualified name should match the module that exposes it.
     * For a package structure like:
     *   timelog/
     *     __init__.py  (imports from _timelog)
     *     _timelog.so  (C extension)
     *
     * We use "timelog._timelog.TimelogError" since CMake installs the
     * extension as timelog/_timelog. Python __init__.py re-exports it
     * as "timelog.TimelogError".
     */
    TlPy_TimelogError = PyErr_NewException(
        "timelog._timelog.TimelogError",  /* name (installed path: timelog/_timelog) */
        NULL,                              /* base (Exception) */
        NULL                               /* dict */
    );

    if (TlPy_TimelogError == NULL) {
        return -1;
    }

    /* Add to module */
    if (PyModule_AddObject(module, "TimelogError", TlPy_TimelogError) < 0) {
        Py_DECREF(TlPy_TimelogError);
        TlPy_TimelogError = NULL;
        return -1;
    }

    /* Note: PyModule_AddObject steals reference on success */
    Py_INCREF(TlPy_TimelogError);

    /*
     * Create TimelogBusyError as a subclass of TimelogError.
     * Used for TL_EBUSY (backpressure / resource busy).
     */
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

/**
 * Map tl_status_t to Python exception type.
 *
 * Mapping rationale:
 * - TL_EINVAL   -> ValueError (bad arguments from user)
 * - TL_ESTATE   -> TimelogError (API usage error)
 * - TL_EBUSY    -> TimelogBusyError (transient, caller should retry)
 * - TL_ENOMEM   -> MemoryError (system resource)
 * - TL_EOVERFLOW-> OverflowError (arithmetic)
 * - TL_EINTERNAL-> SystemError (bug in timelog)
 * - Others      -> TimelogError (catch-all)
 */
static PyObject* status_to_exception_type(tl_status_t status)
{
    switch (status) {
        case TL_EINVAL:
            return PyExc_ValueError;

        case TL_EBUSY:
            /* Transient condition: backpressure, stop in progress, etc. */
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
            /* Use our custom exception for Timelog-specific errors */
            return TlPy_TimelogError ? TlPy_TimelogError : PyExc_RuntimeError;
    }
}

PyObject* TlPy_RaiseFromStatus(tl_status_t status)
{
#ifndef NDEBUG
    /* Defensive: caller should not pass success codes */
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
    /* Defensive: caller should not pass success codes */
    assert(status != TL_OK && status != TL_EOF &&
           "TlPy_RaiseFromStatusFmt called with success status");
#endif

    PyObject* exc_type = status_to_exception_type(status);

    va_list args;
    va_start(args, format);

    /*
     * Build message string.
     * Format: "user message: tl_strerror(status)"
     */
    char buffer[512];
    int n = vsnprintf(buffer, sizeof(buffer) - 64, format, args);
    va_end(args);

    /*
     * Append status message if there's room.
     * Note: n < 0 indicates encoding error; n >= sizeof - 64 means truncated.
     * In both cases, we still set the error with what we have.
     */
    if (n >= 0 && (size_t)n < sizeof(buffer) - 64) {
        const char* status_msg = tl_strerror(status);
        size_t remaining = sizeof(buffer) - (size_t)n;
        snprintf(buffer + n, remaining, ": %s", status_msg);
    }

    PyErr_SetString(exc_type, buffer);
    return NULL;
}
