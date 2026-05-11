/**
 * @file test_py_module_exec.c
 * @brief Direct exec-slot tests for the real timelog module definition.
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_module_state.h"
#include "timelogpy/py_errors.h"

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

static void print_pyerr_context(const char* context)
{
    fprintf(stderr, "Python error during %s\n", context);
    PyErr_Print();
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
            printf("FAIL (unexpected exception)\n"); \
            print_pyerr_context(#name); \
            tests_failed++; \
            return; \
        } \
        printf("PASS\n"); \
    } \
    static void test_##name(void)

#define ASSERT(cond) \
    do { \
        if (!(cond)) { \
            printf("FAIL\n    Assertion failed: %s\n    at %s:%d\n", \
                   #cond, __FILE__, __LINE__); \
            tests_failed++; \
            return; \
        } \
    } while (0)

#define ASSERT_NOT_NULL(ptr) \
    do { \
        if ((ptr) == NULL) { \
            printf("FAIL\n    Expected %s != NULL\n    at %s:%d\n", \
                   #ptr, __FILE__, __LINE__); \
            if (PyErr_Occurred()) { \
                print_pyerr_context(#ptr); \
            } \
            tests_failed++; \
            return; \
        } \
    } while (0)

#define CHECK_GOTO(cond, label) \
    do { \
        if (!(cond)) { \
            printf("FAIL\n    Assertion failed: %s\n    at %s:%d\n", \
                   #cond, __FILE__, __LINE__); \
            tests_failed++; \
            goto label; \
        } \
    } while (0)

static PyObject* get_attr(PyObject* obj, const char* attr_name)
{
    PyObject* attr = PyObject_GetAttrString(obj, attr_name);
    if (attr == NULL) {
        printf("FAIL\n    Expected attribute %s\n    at %s:%d\n",
               attr_name, __FILE__, __LINE__);
        if (PyErr_Occurred()) {
            print_pyerr_context(attr_name);
        }
        tests_failed++;
        return NULL;
    }
    return attr;
}

static int module_attr_absent(PyObject* module, const char* attr_name)
{
    PyObject* attr = PyObject_GetAttrString(module, attr_name);

    if (attr != NULL) {
        Py_DECREF(attr);
        return 0;
    }

    if (PyErr_ExceptionMatches(PyExc_AttributeError)) {
        PyErr_Clear();
        return 1;
    }

    print_pyerr_context(attr_name);
    tests_failed++;
    return -1;
}

static int assert_error_matches_exception_class(PyObject* exc, const char* label)
{
    int matches;

    if (exc == NULL) {
        printf("FAIL\n    Expected exception class %s\n    at %s:%d\n",
               label, __FILE__, __LINE__);
        tests_failed++;
        return -1;
    }

    if (!PyErr_Occurred()) {
        printf("FAIL\n    Expected active exception for %s\n    at %s:%d\n",
               label, __FILE__, __LINE__);
        tests_failed++;
        return -1;
    }

    matches = PyErr_ExceptionMatches(exc);
    if (!matches) {
        printf("FAIL\n    Expected active exception to match %s\n    at %s:%d\n",
               label, __FILE__, __LINE__);
        tests_failed++;
        return -1;
    }

    return 0;
}

static int assert_module_attr_identity(PyObject* module, const char* attr_name, PyObject* expected)
{
    PyObject* attr = get_attr(module, attr_name);
    int matches = 0;

    if (attr == NULL) {
        return -1;
    }

    matches = (attr == expected);
    Py_DECREF(attr);
    if (!matches) {
        printf("FAIL\n    Expected module attribute %s identity to match\n    at %s:%d\n",
               attr_name, __FILE__, __LINE__);
        tests_failed++;
        return -1;
    }
    return 0;
}

static int assert_runtime_error_contains(const char* expected_substring)
{
    PyObject *exc_type = NULL, *exc_value = NULL, *exc_tb = NULL;
    PyObject* exc_text = NULL;
    const char* text = NULL;
    int ok = 0;

    if (!PyErr_Occurred()) {
        printf("FAIL\n    Expected active exception\n    at %s:%d\n", __FILE__, __LINE__);
        tests_failed++;
        return -1;
    }

    if (!PyErr_ExceptionMatches(PyExc_RuntimeError)) {
        printf("FAIL\n    Expected RuntimeError\n    at %s:%d\n", __FILE__, __LINE__);
        tests_failed++;
        return -1;
    }

    PyErr_Fetch(&exc_type, &exc_value, &exc_tb);
    exc_text = PyObject_Str(exc_value != NULL ? exc_value : Py_None);
    if (exc_text != NULL) {
        text = PyUnicode_AsUTF8(exc_text);
    }

    if (text != NULL && strstr(text, expected_substring) != NULL) {
        ok = 1;
    } else {
        printf("FAIL\n    Expected RuntimeError containing \"%s\"\n    at %s:%d\n",
               expected_substring, __FILE__, __LINE__);
        if (text != NULL) {
            printf("    Got: %s\n", text);
        }
        tests_failed++;
    }

    Py_XDECREF(exc_text);
    Py_XDECREF(exc_type);
    Py_XDECREF(exc_value);
    Py_XDECREF(exc_tb);
    return ok ? 0 : -1;
}

static void assert_no_managed_exports(PyObject* module)
{
    ASSERT(module_attr_absent(module, "TimelogError") == 1);
    ASSERT(module_attr_absent(module, "TimelogBusyError") == 1);
    ASSERT(module_attr_absent(module, "Timelog") == 1);
    ASSERT(module_attr_absent(module, "TimelogIter") == 1);
    ASSERT(module_attr_absent(module, "PageSpan") == 1);
    ASSERT(module_attr_absent(module, "PageSpanIter") == 1);
    ASSERT(module_attr_absent(module, "PageSpanObjectsView") == 1);
}

static void assert_public_exports_present(PyObject* module)
{
    PyObject* timelog = get_attr(module, "Timelog");
    PyObject* timelog_iter = get_attr(module, "TimelogIter");
    PyObject* pagespan = get_attr(module, "PageSpan");
    PyObject* pagespan_iter = get_attr(module, "PageSpanIter");
    PyObject* pagespan_objects = get_attr(module, "PageSpanObjectsView");
    PyObject* error = get_attr(module, "TimelogError");
    PyObject* busy_error = get_attr(module, "TimelogBusyError");

    if (timelog == NULL || timelog_iter == NULL || pagespan == NULL ||
        pagespan_iter == NULL || pagespan_objects == NULL ||
        error == NULL || busy_error == NULL) {
        Py_XDECREF(timelog);
        Py_XDECREF(timelog_iter);
        Py_XDECREF(pagespan);
        Py_XDECREF(pagespan_iter);
        Py_XDECREF(pagespan_objects);
        Py_XDECREF(error);
        Py_XDECREF(busy_error);
        return;
    }

    Py_XDECREF(timelog);
    Py_XDECREF(timelog_iter);
    Py_XDECREF(pagespan);
    Py_XDECREF(pagespan_iter);
    Py_XDECREF(pagespan_objects);
    Py_XDECREF(error);
    Py_XDECREF(busy_error);
}

static int assert_state_error_identity(PyObject* module, tl_py_module_state_t* st)
{
    if (st == NULL) {
        printf("FAIL\n    Expected module state\n    at %s:%d\n",
               __FILE__, __LINE__);
        tests_failed++;
        return -1;
    }

    if (st->exc_timelog_error == NULL || st->exc_timelog_busy_error == NULL) {
        printf("FAIL\n    Expected module-state exception pair\n    at %s:%d\n",
               __FILE__, __LINE__);
        tests_failed++;
        return -1;
    }

    if (assert_module_attr_identity(module, "TimelogError", st->exc_timelog_error) < 0) {
        return -1;
    }
    if (assert_module_attr_identity(module, "TimelogBusyError",
                                    st->exc_timelog_busy_error) < 0) {
        return -1;
    }
    return 0;
}

static int set_active_timelog_module(PyObject* module)
{
    PyObject* modules = PyImport_GetModuleDict();
    if (modules == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "sys.modules is unavailable");
        return -1;
    }
    return PyDict_SetItemString(modules, "timelog._timelog", module);
}

static PyObject* new_timelog_instance(PyObject* module)
{
    PyObject* timelog_type = NULL;
    PyObject* instance = NULL;

    if (set_active_timelog_module(module) < 0) {
        return NULL;
    }

    timelog_type = get_attr(module, "Timelog");
    if (timelog_type == NULL) {
        return NULL;
    }

    instance = PyObject_CallNoArgs(timelog_type);
    Py_DECREF(timelog_type);
    return instance;
}

static PyObject* call_noarg_method(PyObject* obj, const char* method_name)
{
    PyObject* method = NULL;
    PyObject* result = NULL;

    method = PyObject_GetAttrString(obj, method_name);
    if (method == NULL) {
        return NULL;
    }
    result = PyObject_CallNoArgs(method);
    Py_DECREF(method);
    return result;
}

static int close_timelog_instance(PyObject* timelog)
{
    PyObject* close_result = call_noarg_method(timelog, "close");
    if (close_result == NULL) {
        return -1;
    }
    Py_DECREF(close_result);
    return 0;
}

TEST(same_module_second_exec_is_noop_success)
{
    PyObject* module = TlPy_Test_CreateModule();
    tl_py_module_state_t* st;
    tl_py_module_state_t* st_after_second_exec;
    PyObject* first_timelog = NULL;
    PyObject* first_iter = NULL;
    PyObject* first_pagespan = NULL;
    PyObject* first_pagespan_iter = NULL;
    PyObject* first_pagespan_objects = NULL;
    PyObject* first_error = NULL;
    PyObject* first_busy_error = NULL;
    PyObject* second_timelog = NULL;
    PyObject* second_iter = NULL;
    PyObject* second_pagespan = NULL;
    PyObject* second_pagespan_iter = NULL;
    PyObject* second_pagespan_objects = NULL;
    PyObject* second_error = NULL;
    PyObject* second_busy_error = NULL;

    ASSERT_NOT_NULL(module);
    ASSERT(TlPy_Test_ModuleStateSize() > 0);
    ASSERT(TlPy_Test_ModuleDeclaresNoSubinterpreters() == 1);

    ASSERT(TlPy_Test_ExecModule(module) == 0);

    st = TlPy_ModuleState(module);
    ASSERT_NOT_NULL(st);
    ASSERT(st->initialized == 1);

    first_timelog = get_attr(module, "Timelog");
    first_iter = get_attr(module, "TimelogIter");
    first_pagespan = get_attr(module, "PageSpan");
    first_pagespan_iter = get_attr(module, "PageSpanIter");
    first_pagespan_objects = get_attr(module, "PageSpanObjectsView");
    first_error = get_attr(module, "TimelogError");
    first_busy_error = get_attr(module, "TimelogBusyError");

    ASSERT(TlPy_Test_ExecModule(module) == 0);
    st_after_second_exec = TlPy_ModuleState(module);
    ASSERT_NOT_NULL(st_after_second_exec);
    ASSERT(st_after_second_exec == st);
    ASSERT(st_after_second_exec->initialized == 1);

    second_timelog = get_attr(module, "Timelog");
    second_iter = get_attr(module, "TimelogIter");
    second_pagespan = get_attr(module, "PageSpan");
    second_pagespan_iter = get_attr(module, "PageSpanIter");
    second_pagespan_objects = get_attr(module, "PageSpanObjectsView");
    second_error = get_attr(module, "TimelogError");
    second_busy_error = get_attr(module, "TimelogBusyError");

    ASSERT(first_timelog == second_timelog);
    ASSERT(first_iter == second_iter);
    ASSERT(first_pagespan == second_pagespan);
    ASSERT(first_pagespan_iter == second_pagespan_iter);
    ASSERT(first_pagespan_objects == second_pagespan_objects);
    ASSERT(first_error == second_error);
    ASSERT(first_busy_error == second_busy_error);

    Py_DECREF(first_timelog);
    Py_DECREF(first_iter);
    Py_DECREF(first_pagespan);
    Py_DECREF(first_pagespan_iter);
    Py_DECREF(first_pagespan_objects);
    Py_DECREF(first_error);
    Py_DECREF(first_busy_error);
    Py_DECREF(second_timelog);
    Py_DECREF(second_iter);
    Py_DECREF(second_pagespan);
    Py_DECREF(second_pagespan_iter);
    Py_DECREF(second_pagespan_objects);
    Py_DECREF(second_error);
    Py_DECREF(second_busy_error);
    Py_DECREF(module);
}

TEST(same_module_reexec_after_manual_reset_preserves_exports)
{
    PyObject* module = TlPy_Test_CreateModule();
    tl_py_module_state_t* st;
    tl_py_module_state_t* st_after_reexec;
    PyObject* first_timelog = NULL;
    PyObject* first_iter = NULL;
    PyObject* first_pagespan = NULL;
    PyObject* first_pagespan_iter = NULL;
    PyObject* first_pagespan_objects = NULL;
    PyObject* first_error = NULL;
    PyObject* first_busy_error = NULL;
    PyObject* second_timelog = NULL;
    PyObject* second_iter = NULL;
    PyObject* second_pagespan = NULL;
    PyObject* second_pagespan_iter = NULL;
    PyObject* second_pagespan_objects = NULL;
    PyObject* second_error = NULL;
    PyObject* second_busy_error = NULL;

    ASSERT_NOT_NULL(module);
    ASSERT(TlPy_Test_ExecModule(module) == 0);

    st = TlPy_ModuleState(module);
    ASSERT_NOT_NULL(st);
    ASSERT(st->initialized == 1);

    first_timelog = get_attr(module, "Timelog");
    first_iter = get_attr(module, "TimelogIter");
    first_pagespan = get_attr(module, "PageSpan");
    first_pagespan_iter = get_attr(module, "PageSpanIter");
    first_pagespan_objects = get_attr(module, "PageSpanObjectsView");
    first_error = get_attr(module, "TimelogError");
    first_busy_error = get_attr(module, "TimelogBusyError");

    ASSERT(first_error == st->exc_timelog_error);
    ASSERT(first_busy_error == st->exc_timelog_busy_error);

    st->initialized = 0;
    ASSERT(TlPy_Test_ExecModule(module) == 0);

    st_after_reexec = TlPy_ModuleState(module);
    ASSERT_NOT_NULL(st_after_reexec);
    ASSERT(st_after_reexec == st);
    ASSERT(st_after_reexec->initialized == 1);

    second_timelog = get_attr(module, "Timelog");
    second_iter = get_attr(module, "TimelogIter");
    second_pagespan = get_attr(module, "PageSpan");
    second_pagespan_iter = get_attr(module, "PageSpanIter");
    second_pagespan_objects = get_attr(module, "PageSpanObjectsView");
    second_error = get_attr(module, "TimelogError");
    second_busy_error = get_attr(module, "TimelogBusyError");

    ASSERT(first_timelog == second_timelog);
    ASSERT(first_iter == second_iter);
    ASSERT(first_pagespan == second_pagespan);
    ASSERT(first_pagespan_iter == second_pagespan_iter);
    ASSERT(first_pagespan_objects == second_pagespan_objects);
    ASSERT(first_error == second_error);
    ASSERT(first_busy_error == second_busy_error);
    ASSERT(second_error == st->exc_timelog_error);
    ASSERT(second_busy_error == st->exc_timelog_busy_error);
    ASSERT(assert_state_error_identity(module, st) == 0);

    Py_DECREF(first_timelog);
    Py_DECREF(first_iter);
    Py_DECREF(first_pagespan);
    Py_DECREF(first_pagespan_iter);
    Py_DECREF(first_pagespan_objects);
    Py_DECREF(first_error);
    Py_DECREF(first_busy_error);
    Py_DECREF(second_timelog);
    Py_DECREF(second_iter);
    Py_DECREF(second_pagespan);
    Py_DECREF(second_pagespan_iter);
    Py_DECREF(second_pagespan_objects);
    Py_DECREF(second_error);
    Py_DECREF(second_busy_error);
    Py_DECREF(module);
}

TEST(retry_after_each_failpoint)
{
    const tl_py_module_failpoint_t failpoints[] = {
        TL_PY_MODULE_FAIL_AFTER_ERRORS,
        TL_PY_MODULE_FAIL_AFTER_EXPORT_TIMELOG,
        TL_PY_MODULE_FAIL_AFTER_EXPORT_ITER,
        TL_PY_MODULE_FAIL_AFTER_EXPORT_PAGESPAN,
        TL_PY_MODULE_FAIL_AFTER_EXPORT_PAGESPAN_ITER,
        TL_PY_MODULE_FAIL_AFTER_EXPORT_PAGESPAN_OBJECTS_VIEW,
        TL_PY_MODULE_FAIL_AFTER_INTERNAL_VIEW_ITER_READY,
    };
    const char* const expected_messages[] = {
        "after errors",
        "after Timelog export",
        "after TimelogIter export",
        "after PageSpan export",
        "after PageSpanIter export",
        "after PageSpanObjectsView export",
        "after PageSpanObjectsViewIter ready",
    };
    size_t i;

    for (i = 0; i < sizeof(failpoints) / sizeof(failpoints[0]); i++) {
        PyObject* module = TlPy_Test_CreateModule();
        tl_py_module_state_t* st;
        PyObject* first_error = NULL;
        PyObject* first_busy_error = NULL;
        int failpoint_armed = 0;
        int failures_before_case = tests_failed;

        CHECK_GOTO(module != NULL, cleanup);

        TlPy_Test_SetExecFailpoint(failpoints[i]);
        failpoint_armed = 1;
        CHECK_GOTO(TlPy_Test_ExecModule(module) < 0, cleanup);
        CHECK_GOTO(assert_runtime_error_contains(expected_messages[i]) == 0, cleanup);

        st = TlPy_ModuleState(module);
        CHECK_GOTO(st != NULL, cleanup);
        CHECK_GOTO(st->initialized == 0, cleanup);
        CHECK_GOTO(st->exc_timelog_error != NULL, cleanup);
        CHECK_GOTO(st->exc_timelog_busy_error != NULL, cleanup);
        first_error = Py_NewRef(st->exc_timelog_error);
        first_busy_error = Py_NewRef(st->exc_timelog_busy_error);
        assert_no_managed_exports(module);
        if (tests_failed != failures_before_case) {
            goto cleanup;
        }

        TlPy_Test_SetExecFailpoint(TL_PY_MODULE_FAIL_NONE);
        failpoint_armed = 0;
        CHECK_GOTO(TlPy_Test_ExecModule(module) == 0, cleanup);
        CHECK_GOTO(st->initialized == 1, cleanup);
        assert_public_exports_present(module);
        CHECK_GOTO(st->exc_timelog_error == first_error, cleanup);
        CHECK_GOTO(st->exc_timelog_busy_error == first_busy_error, cleanup);
        CHECK_GOTO(assert_state_error_identity(module, st) == 0, cleanup);
        if (tests_failed != failures_before_case) {
            goto cleanup;
        }

cleanup:
        if (failpoint_armed) {
            TlPy_Test_SetExecFailpoint(TL_PY_MODULE_FAIL_NONE);
        }
        Py_XDECREF(first_error);
        Py_XDECREF(first_busy_error);
        Py_XDECREF(module);
        if (tests_failed != failures_before_case) {
            return;
        }
    }
}

TEST(two_module_objects_keep_distinct_module_state_and_exceptions)
{
    PyObject* left = TlPy_Test_CreateModule();
    PyObject* right = TlPy_Test_CreateModule();
    PyObject* left_error = NULL;
    PyObject* right_error = NULL;
    tl_py_module_state_t* left_state;
    tl_py_module_state_t* right_state;
    tl_py_module_state_t* right_state_after_retry;

    ASSERT_NOT_NULL(left);
    ASSERT_NOT_NULL(right);

    ASSERT(TlPy_Test_ExecModule(left) == 0);
    left_state = TlPy_ModuleState(left);
    ASSERT_NOT_NULL(left_state);
    ASSERT(left_state->initialized == 1);
    assert_public_exports_present(left);
    assert_no_managed_exports(right);

    TlPy_Test_SetExecFailpoint(TL_PY_MODULE_FAIL_AFTER_EXPORT_TIMELOG);
    ASSERT(TlPy_Test_ExecModule(right) < 0);
    ASSERT(assert_runtime_error_contains("after Timelog export") == 0);
    right_state = TlPy_ModuleState(right);
    ASSERT_NOT_NULL(right_state);
    ASSERT(left_state != right_state);
    ASSERT(right_state->initialized == 0);
    assert_no_managed_exports(right);
    ASSERT(left_state->initialized == 1);
    assert_public_exports_present(left);
    ASSERT(assert_state_error_identity(left, left_state) == 0);

    TlPy_Test_SetExecFailpoint(TL_PY_MODULE_FAIL_NONE);
    ASSERT(TlPy_Test_ExecModule(right) == 0);
    right_state_after_retry = TlPy_ModuleState(right);
    ASSERT_NOT_NULL(right_state_after_retry);
    ASSERT(right_state_after_retry == right_state);
    ASSERT(right_state_after_retry->initialized == 1);
    assert_public_exports_present(left);
    assert_public_exports_present(right);
    ASSERT(assert_state_error_identity(left, left_state) == 0);
    ASSERT(assert_state_error_identity(right, right_state_after_retry) == 0);
    left_error = get_attr(left, "TimelogError");
    right_error = get_attr(right, "TimelogError");
    ASSERT_NOT_NULL(left_error);
    ASSERT_NOT_NULL(right_error);
    ASSERT(left_error == left_state->exc_timelog_error);
    ASSERT(right_error == right_state_after_retry->exc_timelog_error);
    ASSERT(left_error != right_error);

    Py_DECREF(left_error);
    Py_DECREF(right_error);
    Py_DECREF(left);
    Py_DECREF(right);
}

TEST(dual_module_timelog_instances_keep_runtime_exception_context)
{
    PyObject* left = TlPy_Test_CreateModule();
    PyObject* right = TlPy_Test_CreateModule();
    PyObject* left_obj = NULL;
    PyObject* right_obj = NULL;
    tl_py_module_state_t* left_state;
    tl_py_module_state_t* right_state;

    ASSERT_NOT_NULL(left);
    ASSERT_NOT_NULL(right);
    ASSERT(TlPy_Test_ExecModule(left) == 0);
    ASSERT(TlPy_Test_ExecModule(right) == 0);

    left_state = TlPy_ModuleState(left);
    right_state = TlPy_ModuleState(right);
    ASSERT_NOT_NULL(left_state);
    ASSERT_NOT_NULL(right_state);
    ASSERT(left_state != right_state);
    ASSERT(left_state->exc_timelog_error != right_state->exc_timelog_error);

    left_obj = new_timelog_instance(left);
    ASSERT_NOT_NULL(left_obj);
    right_obj = new_timelog_instance(right);
    ASSERT_NOT_NULL(right_obj);

    ASSERT(close_timelog_instance(left_obj) == 0);
    ASSERT(close_timelog_instance(right_obj) == 0);

    ASSERT(call_noarg_method(left_obj, "flush") == NULL);
    ASSERT(assert_error_matches_exception_class(left_state->exc_timelog_error,
                                               "left TimelogError") == 0);
    PyErr_Clear();

    ASSERT(call_noarg_method(right_obj, "flush") == NULL);
    ASSERT(assert_error_matches_exception_class(right_state->exc_timelog_error,
                                               "right TimelogError") == 0);
    PyErr_Clear();

    Py_DECREF(left_obj);
    Py_DECREF(right_obj);
    Py_DECREF(left);
    Py_DECREF(right);
}

int main(void)
{
    tlpy_init_python();

    printf("Running direct module exec tests:\n\n");

    run_same_module_second_exec_is_noop_success();
    run_same_module_reexec_after_manual_reset_preserves_exports();
    run_retry_after_each_failpoint();
    run_two_module_objects_keep_distinct_module_state_and_exceptions();
    run_dual_module_timelog_instances_keep_runtime_exception_context();

    printf("\nSummary: %d run, %d failed\n", tests_run, tests_failed);

    if (tlpy_finalize_python() < 0) {
        fprintf(stderr, "Py_FinalizeEx failed\n");
        return 1;
    }

    return tests_failed == 0 ? 0 : 1;
}
