/**
 * @file test_py_errors.c
 * @brief Error subsystem tests for module-local exception ownership
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_errors.h"
#include "timelogpy/py_module_state.h"
#include "timelog/timelog.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int tests_run = 0;
static int tests_failed = 0;

static void tlpy_set_pythonhome(void)
{
#ifdef TIMELOG_PYTHON_EXECUTABLE
    const char* existing = getenv("PYTHONHOME");
    if (existing != NULL && existing[0] != '\0') {
        return;
    }

    const char* exe = TIMELOG_PYTHON_EXECUTABLE;
    size_t len = strlen(exe);
    char* buf = (char*)malloc(len + 1);
    if (buf == NULL) {
        return;
    }
    memcpy(buf, exe, len + 1);

    char* last_slash = strrchr(buf, '\\');
    char* last_fwd = strrchr(buf, '/');
    char* last = last_slash;
    if (last_fwd != NULL && (last == NULL || last_fwd > last)) {
        last = last_fwd;
    }
    if (last != NULL) {
        *last = '\0';
#ifdef _WIN32
        _putenv_s("PYTHONHOME", buf);
#else
        setenv("PYTHONHOME", buf, 0);
#endif
    }
    free(buf);
#endif
}

static void tlpy_init_python(void)
{
    tlpy_set_pythonhome();
    Py_Initialize();
}

static int tlpy_finalize_python(void)
{
    return Py_FinalizeEx();
}

#define TEST(name) \
    static void test_##name(void); \
    static void run_##name(void) { \
        printf("  %s... ", #name); \
        fflush(stdout); \
        tests_run++; \
        PyErr_Clear(); \
        test_##name(); \
        if (PyErr_Occurred()) { \
            printf("FAIL (unexpected exception)\\n"); \
            PyErr_Print(); \
            tests_failed++; \
            return; \
        } \
        printf("PASS\\n"); \
    } \
    static void test_##name(void)

#define ASSERT(cond) \
    do { \
        if (!(cond)) { \
            printf("FAIL\\n    Assertion failed: %s\\n    at %s:%d\\n", \
                   #cond, __FILE__, __LINE__); \
            tests_failed++; \
            return; \
        } \
    } while (0)

#define ASSERT_NOT_NULL(ptr) \
    do { \
        if ((ptr) == NULL) { \
            printf("FAIL\\n    Expected %s != NULL\\n    at %s:%d\\n", \
                   #ptr, __FILE__, __LINE__); \
            if (PyErr_Occurred()) { \
                PyErr_Print(); \
            } \
            tests_failed++; \
            return; \
        } \
    } while (0)

#define ASSERT_EXCEPTION(exc_type) \
    do { \
        if (!PyErr_Occurred()) { \
            printf("FAIL\\n    Expected exception %s\\n    at %s:%d\\n", \
                   #exc_type, __FILE__, __LINE__); \
            tests_failed++; \
            return; \
        } \
        if (!PyErr_ExceptionMatches((exc_type))) { \
            printf("FAIL\\n    Expected exception %s\\n    at %s:%d\\n", \
                   #exc_type, __FILE__, __LINE__); \
            PyErr_Print(); \
            tests_failed++; \
            return; \
        } \
        PyErr_Clear(); \
    } while (0)

static struct PyModuleDef test_module_def = {
    .m_base = PyModuleDef_HEAD_INIT,
    .m_name = "timelog._timelog",
    .m_doc = NULL,
    .m_size = sizeof(tl_py_module_state_t),
    .m_methods = NULL,
    .m_slots = NULL,
    .m_traverse = NULL,
    .m_clear = NULL,
    .m_free = NULL,
};

static PyObject* create_error_module(tl_py_module_state_t** out_state)
{
    PyObject* module = PyModule_Create(&test_module_def);
    tl_py_module_state_t* st = NULL;

    if (module == NULL) {
        return NULL;
    }

    st = TlPy_ModuleState(module);
    if (st == NULL) {
        Py_DECREF(module);
        PyErr_SetString(PyExc_RuntimeError, "test module state is unavailable");
        return NULL;
    }

    if (TlPy_InitErrors(module, st) < 0) {
        Py_DECREF(module);
        return NULL;
    }
    if (PyModule_AddObjectRef(module, "TimelogError", st->exc_timelog_error) < 0 ||
        PyModule_AddObjectRef(module, "TimelogBusyError",
                              st->exc_timelog_busy_error) < 0) {
        Py_DECREF(module);
        return NULL;
    }

    if (out_state != NULL) {
        *out_state = st;
    }
    return module;
}

TEST(init_creates_module_owned_exception_pair)
{
    PyObject* module = NULL;
    PyObject* error = NULL;
    PyObject* busy = NULL;
    tl_py_module_state_t* st = NULL;

    module = create_error_module(&st);
    ASSERT_NOT_NULL(module);
    ASSERT_NOT_NULL(st);
    ASSERT(st->exc_timelog_error != NULL);
    ASSERT(st->exc_timelog_busy_error != NULL);

    error = PyObject_GetAttrString(module, "TimelogError");
    busy = PyObject_GetAttrString(module, "TimelogBusyError");
    ASSERT_NOT_NULL(error);
    ASSERT_NOT_NULL(busy);
    ASSERT(error == st->exc_timelog_error);
    ASSERT(busy == st->exc_timelog_busy_error);

    Py_DECREF(error);
    Py_DECREF(busy);
    Py_DECREF(module);
}

TEST(busy_error_subclasses_timelog_error)
{
    PyObject* module = NULL;
    tl_py_module_state_t* st = NULL;
    int is_subclass;

    module = create_error_module(&st);
    ASSERT_NOT_NULL(module);
    ASSERT_NOT_NULL(st);

    is_subclass = PyObject_IsSubclass(st->exc_timelog_busy_error,
                                      st->exc_timelog_error);
    ASSERT(is_subclass == 1);

    Py_DECREF(module);
}

TEST(clear_errors_clears_state_owned_refs)
{
    PyObject* module = NULL;
    PyObject* error = NULL;
    PyObject* exported_error = NULL;
    tl_py_module_state_t* st = NULL;

    module = create_error_module(&st);
    ASSERT_NOT_NULL(module);
    ASSERT_NOT_NULL(st);
    error = PyObject_GetAttrString(module, "TimelogError");
    ASSERT_NOT_NULL(error);

    TlPy_ClearErrors(st);
    ASSERT(st->exc_timelog_error == NULL);
    ASSERT(st->exc_timelog_busy_error == NULL);
    exported_error = PyObject_GetAttrString(module, "TimelogError");
    ASSERT_NOT_NULL(exported_error);

    Py_DECREF(exported_error);
    Py_DECREF(error);
    Py_DECREF(module);
}

TEST(reinit_after_clear_recreates_cleanly)
{
    PyObject* module = NULL;
    PyObject* first_error = NULL;
    tl_py_module_state_t* st = NULL;

    module = create_error_module(&st);
    ASSERT_NOT_NULL(module);
    ASSERT_NOT_NULL(st);

    first_error = Py_NewRef(st->exc_timelog_error);
    TlPy_ClearErrors(st);
    ASSERT(st->exc_timelog_error == NULL);
    ASSERT(st->exc_timelog_busy_error == NULL);

    ASSERT(TlPy_InitErrors(module, st) == 0);
    ASSERT(st->exc_timelog_error != NULL);
    ASSERT(st->exc_timelog_busy_error != NULL);
    ASSERT(st->exc_timelog_error != first_error);

    Py_DECREF(first_error);
    Py_DECREF(module);
}

TEST(state_reports_complete_error_pair)
{
    PyObject* module = NULL;
    tl_py_module_state_t* st = NULL;

    module = create_error_module(&st);
    ASSERT_NOT_NULL(module);
    ASSERT_NOT_NULL(st);
    ASSERT(TlPy_StateHasCompleteErrors(st));
    Py_DECREF(module);
}

TEST(raise_estate_uses_module_timelog_error)
{
    PyObject* module = NULL;
    tl_py_module_state_t* st = NULL;

    module = create_error_module(&st);
    ASSERT_NOT_NULL(module);

    ASSERT(TlPy_RaiseFromState(st, TL_ESTATE) == NULL);
    ASSERT_EXCEPTION(st->exc_timelog_error);

    Py_DECREF(module);
}

TEST(raise_busy_uses_module_busy_error)
{
    PyObject* module = NULL;
    tl_py_module_state_t* st = NULL;

    module = create_error_module(&st);
    ASSERT_NOT_NULL(module);

    ASSERT(TlPy_RaiseFromState(st, TL_EBUSY) == NULL);
    ASSERT_EXCEPTION(st->exc_timelog_busy_error);

    Py_DECREF(module);
}

TEST(raise_unknown_uses_timelog_error)
{
    PyObject* module = NULL;
    tl_py_module_state_t* st = NULL;

    module = create_error_module(&st);
    ASSERT_NOT_NULL(module);

    ASSERT(TlPy_RaiseFromState(st, (tl_status_t)999) == NULL);
    ASSERT_EXCEPTION(st->exc_timelog_error);

    Py_DECREF(module);
}

TEST(raise_formatted_appends_status_message)
{
    PyObject* module = NULL;
    tl_py_module_state_t* st = NULL;
    PyObject *exc_type = NULL, *exc_value = NULL, *exc_tb = NULL;
    PyObject* exc_text = NULL;
    const char* text = NULL;

    module = create_error_module(&st);
    ASSERT_NOT_NULL(module);

    ASSERT(TlPy_RaiseFromStateFmt(st, TL_ESTATE, "custom context") == NULL);
    ASSERT(PyErr_ExceptionMatches(st->exc_timelog_error));

    PyErr_Fetch(&exc_type, &exc_value, &exc_tb);
    exc_text = PyObject_Str(exc_value != NULL ? exc_value : Py_None);
    ASSERT_NOT_NULL(exc_text);
    text = PyUnicode_AsUTF8(exc_text);
    ASSERT(text != NULL);
    ASSERT(strstr(text, "custom context") != NULL);
    /* v1.3: custom messages stand alone — the status is encoded in the
     * exception type; no ": invalid state" suffix (usability lab). */
    ASSERT(strstr(text, tl_strerror(TL_ESTATE)) == NULL);

    Py_XDECREF(exc_text);
    Py_XDECREF(exc_type);
    Py_XDECREF(exc_value);
    Py_XDECREF(exc_tb);
    Py_DECREF(module);
}

TEST(raise_formatted_empty_format_still_sets_status_text)
{
    PyObject* module = NULL;
    tl_py_module_state_t* st = NULL;
    PyObject *exc_type = NULL, *exc_value = NULL, *exc_tb = NULL;
    PyObject* exc_text = NULL;
    const char* text = NULL;

    module = create_error_module(&st);
    ASSERT_NOT_NULL(module);

    ASSERT(TlPy_RaiseFromStateFmt(st, TL_ESTATE, "") == NULL);
    ASSERT(PyErr_ExceptionMatches(st->exc_timelog_error));

    PyErr_Fetch(&exc_type, &exc_value, &exc_tb);
    exc_text = PyObject_Str(exc_value != NULL ? exc_value : Py_None);
    ASSERT_NOT_NULL(exc_text);
    text = PyUnicode_AsUTF8(exc_text);
    ASSERT(text != NULL);
    ASSERT(strstr(text, tl_strerror(TL_ESTATE)) != NULL);

    Py_XDECREF(exc_text);
    Py_XDECREF(exc_type);
    Py_XDECREF(exc_value);
    Py_XDECREF(exc_tb);
    Py_DECREF(module);
}

TEST(raise_formatted_long_message_is_preserved)
{
    PyObject* module = NULL;
    tl_py_module_state_t* st = NULL;
    PyObject *exc_type = NULL, *exc_value = NULL, *exc_tb = NULL;
    PyObject* exc_text = NULL;
    const char* text = NULL;
    char long_msg[2048];

    memset(long_msg, 'x', sizeof(long_msg) - 1);
    long_msg[sizeof(long_msg) - 1] = '\0';

    module = create_error_module(&st);
    ASSERT_NOT_NULL(module);

    ASSERT(TlPy_RaiseFromStateFmt(st, TL_ESTATE, "%s", long_msg) == NULL);
    ASSERT(PyErr_ExceptionMatches(st->exc_timelog_error));

    PyErr_Fetch(&exc_type, &exc_value, &exc_tb);
    exc_text = PyObject_Str(exc_value != NULL ? exc_value : Py_None);
    ASSERT_NOT_NULL(exc_text);
    text = PyUnicode_AsUTF8(exc_text);
    ASSERT(text != NULL);
    /* PyErr_FormatV imposes no fixed buffer: the FULL message survives. */
    ASSERT(strcmp(text, long_msg) == 0);
    ASSERT(strlen(text) == sizeof(long_msg) - 1);

    Py_XDECREF(exc_text);
    Py_XDECREF(exc_type);
    Py_XDECREF(exc_value);
    Py_XDECREF(exc_tb);
    Py_DECREF(module);
}

TEST(runtime_fallback_without_state_uses_runtimeerror)
{
    ASSERT(TlPy_RaiseFromState(NULL, TL_ESTATE) == NULL);
    ASSERT_EXCEPTION(PyExc_RuntimeError);

    ASSERT(TlPy_RaiseFromState(NULL, TL_EBUSY) == NULL);
    ASSERT_EXCEPTION(PyExc_RuntimeError);
}

int main(void)
{
    tlpy_init_python();

    printf("Running py_errors tests...\\n\\n");
    run_init_creates_module_owned_exception_pair();
    run_busy_error_subclasses_timelog_error();
    run_clear_errors_clears_state_owned_refs();
    run_reinit_after_clear_recreates_cleanly();
    run_state_reports_complete_error_pair();
    run_raise_estate_uses_module_timelog_error();
    run_raise_busy_uses_module_busy_error();
    run_raise_unknown_uses_timelog_error();
    run_raise_formatted_appends_status_message();
    run_raise_formatted_empty_format_still_sets_status_text();
    run_raise_formatted_long_message_is_preserved();
    run_runtime_fallback_without_state_uses_runtimeerror();

    printf("\\nSummary: %d run, %d failed\\n", tests_run, tests_failed);

    if (tlpy_finalize_python() < 0) {
        fprintf(stderr, "Py_FinalizeEx failed\\n");
        return 1;
    }

    return tests_failed == 0 ? 0 : 1;
}
