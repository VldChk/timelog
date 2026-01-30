/**
 * @file py_errors.h
 * @brief Error translation from Timelog status codes to Python exceptions
 *
 * This module provides consistent mapping from tl_status_t codes to
 * appropriate Python exception types.
 *
 * Mapping (actual implementation):
 * - TL_OK / TL_EOF   -> No exception (success)
 * - TL_EINVAL        -> ValueError
 * - TL_ESTATE        -> TimelogError (API usage error)
 * - TL_EBUSY         -> TimelogBusyError (context-dependent busy/backpressure)
 * - TL_ENOMEM        -> MemoryError
 * - TL_EOVERFLOW     -> OverflowError
 * - TL_EINTERNAL     -> SystemError (bug in timelog)
 * - (other)          -> TimelogError (catch-all)
 */

#ifndef TL_PY_ERRORS_H
#define TL_PY_ERRORS_H

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelog/timelog.h"

#ifdef __cplusplus
extern "C" {
#endif

/*===========================================================================
 * Custom Exception Type
 *
 * We define a TimelogError base exception for Timelog-specific errors.
 * Subclasses map to specific tl_status_t categories.
 *===========================================================================*/

/**
 * Base exception for all Timelog errors.
 * Inherits from Exception.
 *
 * This is initialized during module init and must be called before
 * any error translation functions.
 */
extern PyObject* TlPy_TimelogError;

/**
 * Exception for resource busy / backpressure conditions (TL_EBUSY).
 * Inherits from TimelogError.
 *
 * IMPORTANT: Context-dependent semantics:
 * - For WRITE operations (append, extend, delete_range, delete_before):
 *   The write WAS accepted, but backpressure occurred. DO NOT RETRY -
 *   retrying would create duplicate records. Call flush() in manual mode,
 *   or wait for background maintenance to catch up.
 * - For tl_flush()/tl_compact()/tl_maint_step(): publish retry exhausted;
 *   no data loss, safe to retry later.
 * - For start_maintenance(): stop in progress - retry later is safe.
 *
 * Typical causes:
 * - Sealed memrun queue is full (backpressure)
 * - OOO head flush failed after insert (runset pressure)
 * - Publish retry exhausted (flush/maintenance)
 * - Maintenance stop in progress
 */
extern PyObject* TlPy_TimelogBusyError;

/**
 * Initialize exception types.
 * Must be called during module initialization (PyInit_...).
 *
 * @param module The module object to add exceptions to
 * @return 0 on success, -1 on failure (with Python exception set)
 */
int TlPy_InitErrors(PyObject* module);

/**
 * Clean up exception types.
 * Called during module deallocation.
 */
void TlPy_FiniErrors(void);

/*===========================================================================
 * Error Translation API
 *===========================================================================*/

/**
 * Raise a Python exception from a tl_status_t code.
 *
 * Sets the appropriate Python exception based on the status code.
 * Returns NULL for convenient use in return statements.
 *
 * @param status Timelog status code (should not be TL_OK or TL_EOF)
 * @return NULL (always)
 *
 * Usage:
 *   if (st != TL_OK) return TlPy_RaiseFromStatus(st);
 */
PyObject* TlPy_RaiseFromStatus(tl_status_t status);

/**
 * Raise a Python exception with custom message format.
 *
 * @param status Timelog status code
 * @param format Printf-style format string
 * @param ...    Format arguments
 * @return NULL (always)
 */
PyObject* TlPy_RaiseFromStatusFmt(tl_status_t status,
                                   const char* format, ...);

/**
 * Check if a status code indicates success (TL_OK or TL_EOF).
 *
 * @param status Timelog status code
 * @return 1 if success, 0 if error
 */
static inline int TlPy_StatusOK(tl_status_t status) {
    return status == TL_OK || status == TL_EOF;
}

#ifdef __cplusplus
}
#endif

#endif /* TL_PY_ERRORS_H */
