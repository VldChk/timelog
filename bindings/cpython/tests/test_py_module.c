/**
 * @file test_py_module.c
 * @brief Black-box module import tests for the built timelog package.
 *
 * Scope:
 * - import/init smoke for timelog._timelog
 * - repeated import stability inside one interpreter
 * - exported-name sanity for extension and top-level package
 * - fresh re-import after sys.modules eviction
 *
 * This target intentionally imports the built package under embedded Python
 * instead of reaching into future multi-phase-init internals.
 *
 * NOTE:
 * Same-module timelog_exec() idempotence is covered by test_py_module_exec.c.
 * This file remains the black-box import/package smoke target.
 */

#include "py_test_harness.h"

static void print_pyerr_context(const char* context)
{
    fprintf(stderr, "Python error during %s\n", context);
    PyErr_Print();
}

static PyObject* import_module(const char* name)
{
    PyObject* module = PyImport_ImportModule(name);
    if (module == NULL) {
        print_pyerr_context(name);
    }
    return module;
}

static void assert_attr_exists(PyObject* obj, const char* attr_name)
{
    PyObject* attr = PyObject_GetAttrString(obj, attr_name);
    ASSERT_NOT_NULL(attr);
    Py_DECREF(attr);
}

static void assert_attr_identity(PyObject* left, const char* left_attr,
                                 PyObject* right, const char* right_attr)
{
    PyObject* left_obj = PyObject_GetAttrString(left, left_attr);
    PyObject* right_obj = PyObject_GetAttrString(right, right_attr);

    ASSERT_NOT_NULL(left_obj);
    ASSERT_NOT_NULL(right_obj);
    if (left_obj == NULL || right_obj == NULL) {
        Py_XDECREF(left_obj);
        Py_XDECREF(right_obj);
        return;
    }
    ASSERT(left_obj == right_obj);

    Py_DECREF(left_obj);
    Py_DECREF(right_obj);
}

static void remove_from_sys_modules(const char* name)
{
    PyObject* modules = PyImport_GetModuleDict();

    ASSERT_NOT_NULL(modules);
    if (PyDict_DelItemString(modules, name) < 0) {
        PyErr_Clear();
    }
}

static void assert_all_contains(PyObject* package, const char* attr_name)
{
    PyObject* all_obj = PyObject_GetAttrString(package, "__all__");
    PyObject* item = NULL;
    int contains = 0;

    ASSERT_NOT_NULL(all_obj);
    if (all_obj == NULL) {
        return;
    }

    item = PyUnicode_FromString(attr_name);
    ASSERT_NOT_NULL(item);
    if (item == NULL) {
        Py_DECREF(all_obj);
        return;
    }

    contains = PySequence_Contains(all_obj, item);
    ASSERT(contains == 1);

    Py_DECREF(item);
    Py_DECREF(all_obj);
}

TEST(extension_import_smoke)
{
    PyObject* module = import_module("timelog._timelog");
    ASSERT_NOT_NULL(module);
    Py_DECREF(module);
}

TEST(repeated_import_same_module_object)
{
    PyObject* first = import_module("timelog._timelog");
    PyObject* second = import_module("timelog._timelog");

    ASSERT_NOT_NULL(first);
    ASSERT_NOT_NULL(second);
    ASSERT(first == second);

    Py_DECREF(first);
    Py_DECREF(second);
}

TEST(extension_exports_expected_names)
{
    PyObject* module = import_module("timelog._timelog");
    ASSERT_NOT_NULL(module);

    assert_attr_exists(module, "Timelog");
    assert_attr_exists(module, "TimelogIter");
    assert_attr_exists(module, "PageSpan");
    assert_attr_exists(module, "PageSpanIter");
    assert_attr_exists(module, "PageSpanObjectsView");
    assert_attr_exists(module, "TimelogError");
    assert_attr_exists(module, "TimelogBusyError");

    Py_DECREF(module);
}

TEST(top_level_package_import_sanity)
{
    PyObject* package = import_module("timelog");
    PyObject* extension = import_module("timelog._timelog");
    ASSERT_NOT_NULL(package);
    ASSERT_NOT_NULL(extension);

    assert_attr_exists(package, "Timelog");
    assert_attr_exists(package, "TimelogError");
    assert_attr_exists(package, "TimelogBusyError");
    assert_attr_exists(package, "PageSpan");
    assert_attr_exists(package, "__version__");
    assert_attr_exists(extension, "Timelog");

    Py_DECREF(package);
    Py_DECREF(extension);
}

TEST(fresh_reimport_after_sys_modules_eviction)
{
    PyObject* first_package = import_module("timelog");
    PyObject* first_extension = import_module("timelog._timelog");
    PyObject* second_package;
    PyObject* second_extension;
    PyObject* package_timelog = NULL;
    PyObject* extension_timelog = NULL;

    ASSERT_NOT_NULL(first_package);
    ASSERT_NOT_NULL(first_extension);

    remove_from_sys_modules("timelog._timelog");
    remove_from_sys_modules("timelog");

    second_package = import_module("timelog");
    second_extension = import_module("timelog._timelog");

    ASSERT_NOT_NULL(second_package);
    ASSERT_NOT_NULL(second_extension);
    ASSERT(first_package != second_package);
    ASSERT(first_extension != second_extension);

    assert_attr_exists(second_package, "Timelog");
    assert_attr_exists(second_package, "TimelogError");
    assert_attr_exists(second_package, "TimelogBusyError");
    assert_attr_exists(second_package, "TimelogIter");
    assert_attr_exists(second_package, "PageSpan");
    assert_attr_exists(second_package, "PageSpanIter");
    assert_attr_exists(second_package, "PageSpanObjectsView");
    assert_attr_exists(second_package, "__version__");
    assert_attr_exists(second_package, "__all__");
    assert_attr_exists(second_extension, "Timelog");
    assert_attr_identity(second_package, "TimelogError", second_extension, "TimelogError");
    assert_attr_identity(second_package, "TimelogBusyError", second_extension, "TimelogBusyError");
    assert_attr_identity(second_package, "TimelogIter", second_extension, "TimelogIter");
    assert_attr_identity(second_package, "PageSpan", second_extension, "PageSpan");
    assert_attr_identity(second_package, "PageSpanIter", second_extension, "PageSpanIter");
    assert_attr_identity(second_package, "PageSpanObjectsView", second_extension, "PageSpanObjectsView");
    assert_all_contains(second_package, "Timelog");
    assert_all_contains(second_package, "TimelogError");
    assert_all_contains(second_package, "TimelogBusyError");
    assert_all_contains(second_package, "TimelogIter");
    assert_all_contains(second_package, "PageSpan");
    assert_all_contains(second_package, "PageSpanIter");
    assert_all_contains(second_package, "PageSpanObjectsView");
    assert_all_contains(second_package, "__version__");

    package_timelog = PyObject_GetAttrString(second_package, "Timelog");
    extension_timelog = PyObject_GetAttrString(second_extension, "Timelog");
    ASSERT_NOT_NULL(package_timelog);
    ASSERT_NOT_NULL(extension_timelog);
    ASSERT(PyObject_IsSubclass(package_timelog, extension_timelog) == 1);

    Py_DECREF(first_package);
    Py_DECREF(first_extension);
    Py_DECREF(package_timelog);
    Py_DECREF(extension_timelog);
    Py_DECREF(second_package);
    Py_DECREF(second_extension);
}

int main(void)
{
    tlpy_init_python();

    printf("Running module import tests:\n\n");

    run_extension_import_smoke();
    run_repeated_import_same_module_object();
    run_extension_exports_expected_names();
    run_top_level_package_import_sanity();
    run_fresh_reimport_after_sys_modules_eviction();

    return tlpy_test_report();
}
