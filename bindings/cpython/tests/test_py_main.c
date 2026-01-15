/**
 * @file test_py_main.c
 * @brief Documentation for running all CPython binding tests
 *
 * RECOMMENDED: Use CTest to run all tests:
 *
 *   cd build
 *   ctest -C Release --output-on-failure
 *
 * Or use the custom target (config is automatic):
 *
 *   cmake --build build --config Release --target run_all_tests
 *
 * NOTE: The -C <config> flag is REQUIRED for multi-config generators (MSVC).
 * Without it, ctest reports "Not Run" because it can't find the executables.
 *
 * Individual test executables (in build/<Config>/):
 *   - test_py_handle.exe   (LLD-B1: Handle context and pin protocol)
 *   - test_py_timelog.exe  (LLD-B2: Timelog type and factory methods)
 *   - test_py_iter.exe     (LLD-B3: Iterator protocol)
 *   - test_py_span.exe     (LLD-B4: PageSpan zero-copy buffer protocol)
 *
 * This file exists as documentation. The actual test runner is CTest.
 */

/* This file is not compiled into an executable */
#error "This file is documentation only. Use 'ctest' to run all tests."
