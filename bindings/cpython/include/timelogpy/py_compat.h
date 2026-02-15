#ifndef TIMELOGPY_PY_COMPAT_H
#define TIMELOGPY_PY_COMPAT_H

#include <Python.h>

/* Python 3.12 fallback for Py_IsFinalizing (3.13+ public API). */
#if PY_VERSION_HEX < 0x030D0000
static inline int tl_py_is_finalizing_compat(void)
{
    PyObject* func = PySys_GetObject("is_finalizing"); /* borrowed */
    if (func == NULL) {
        return 1;
    }
    PyObject* res = PyObject_CallNoArgs(func);
    if (res == NULL) {
        PyErr_Clear();
        return 1;
    }
    int is_final = PyObject_IsTrue(res);
    Py_DECREF(res);
    if (is_final < 0) {
        PyErr_Clear();
        return 1;
    }
    return is_final;
}
#define TL_PY_IS_FINALIZING() tl_py_is_finalizing_compat()
#else
#define TL_PY_IS_FINALIZING() Py_IsFinalizing()
#endif

#endif /* TIMELOGPY_PY_COMPAT_H */
