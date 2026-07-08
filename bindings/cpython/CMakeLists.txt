# =============================================================================
# Timelog Python Bindings (CPython Extension)
# =============================================================================
#
# Included from the root timelog CMakeLists.txt via add_subdirectory() when
# TIMELOG_BUILD_PYTHON=ON (the default). There is no standalone build mode;
# configure the repository root:
#
#   cmake -B build -DTIMELOG_BUILD_PYTHON=ON
#   cmake --build build
#

cmake_minimum_required(VERSION 3.15)
if(POLICY CMP0177)
    cmake_policy(SET CMP0177 NEW)
endif()

# Root build enables warnings-as-errors globally for core. Disable that policy
# in bindings so Python/C API header warnings do not break extension builds.
if(MSVC)
    add_compile_options(/WX-)
else()
    add_compile_options(-Wno-error)
endif()

# =============================================================================
# Find Python
# =============================================================================

# Wheel builds only need extension-module headers/tooling. Embedded-Python C
# tests need embed libraries as well. Request components accordingly.
if(TIMELOG_BUILD_PY_TESTS)
    find_package(Python3 REQUIRED COMPONENTS Interpreter Development.Module Development.Embed)
else()
    find_package(Python3 REQUIRED COMPONENTS Interpreter Development.Module)
endif()

message(STATUS "Python3 found: ${Python3_EXECUTABLE}")
message(STATUS "Python3 include: ${Python3_INCLUDE_DIRS}")
message(STATUS "Python3 libraries: ${Python3_LIBRARIES}")

set(TIMELOG_PY_GIL_DISABLED 0)
if(Python3_EXECUTABLE)
    execute_process(
        COMMAND "${Python3_EXECUTABLE}" -c
                "import sysconfig; print(1 if sysconfig.get_config_var('Py_GIL_DISABLED') else 0)"
        RESULT_VARIABLE _timelog_py_gil_disabled_rc
        OUTPUT_VARIABLE _timelog_py_gil_disabled_out
        OUTPUT_STRIP_TRAILING_WHITESPACE
        ERROR_QUIET
    )
    if(_timelog_py_gil_disabled_rc EQUAL 0 AND
       _timelog_py_gil_disabled_out STREQUAL "1")
        set(TIMELOG_PY_GIL_DISABLED 1)
    endif()
endif()

if(TIMELOG_PY_GIL_DISABLED)
    add_compile_definitions(Py_GIL_DISABLED=1)
    message(STATUS "Python3 free-threaded build detected: defining Py_GIL_DISABLED=1 for CPython bindings")
endif()

# Ensure embedded-Python test executables can locate the Python runtime DLL.
if(WIN32)
    set(_PYTHON_RUNTIME_DLL_RELEASE "")
    set(_PYTHON_RUNTIME_DLL_DEBUG "")

    if(DEFINED Python3_RUNTIME_LIBRARY_RELEASE)
        set(_PYTHON_RUNTIME_DLL_RELEASE "${Python3_RUNTIME_LIBRARY_RELEASE}")
    elseif(DEFINED Python3_RUNTIME_LIBRARY)
        set(_PYTHON_RUNTIME_DLL_RELEASE "${Python3_RUNTIME_LIBRARY}")
    elseif(DEFINED _Python3_RUNTIME_LIBRARY_RELEASE)
        set(_PYTHON_RUNTIME_DLL_RELEASE "${_Python3_RUNTIME_LIBRARY_RELEASE}")
    endif()

    if(DEFINED Python3_RUNTIME_LIBRARY_DEBUG)
        set(_PYTHON_RUNTIME_DLL_DEBUG "${Python3_RUNTIME_LIBRARY_DEBUG}")
    elseif(DEFINED _Python3_RUNTIME_LIBRARY_DEBUG)
        set(_PYTHON_RUNTIME_DLL_DEBUG "${_Python3_RUNTIME_LIBRARY_DEBUG}")
    endif()

    if(NOT _PYTHON_RUNTIME_DLL_RELEASE)
        get_filename_component(_PYTHON_DIR "${Python3_EXECUTABLE}" DIRECTORY)
        set(_PYTHON_RUNTIME_DLL_RELEASE
            "${_PYTHON_DIR}/python${Python3_VERSION_MAJOR}${Python3_VERSION_MINOR}.dll")
    endif()

    if(NOT _PYTHON_RUNTIME_DLL_DEBUG)
        set(_PYTHON_RUNTIME_DLL_DEBUG "${_PYTHON_RUNTIME_DLL_RELEASE}")
    endif()

    function(timelog_copy_python_runtime target)
        if(EXISTS "${_PYTHON_RUNTIME_DLL_RELEASE}")
            add_custom_command(TARGET ${target} POST_BUILD
                COMMAND ${CMAKE_COMMAND} -E copy_if_different
                        "$<$<CONFIG:Debug>:${_PYTHON_RUNTIME_DLL_DEBUG}>$<$<NOT:$<CONFIG:Debug>>:${_PYTHON_RUNTIME_DLL_RELEASE}>"
                        "$<TARGET_FILE_DIR:${target}>"
            )
        else()
            message(WARNING "Python runtime DLL not found; ${target} may fail to run without PATH set.")
        endif()
    endfunction()
else()
    function(timelog_copy_python_runtime target)
    endfunction()
endif()

# =============================================================================
# Python Extension Module: _timelog
# =============================================================================

set(TIMELOG_PY_SOURCES
    src/py_handle.c
    src/py_errors.c
    src/py_timelog.c    # PyTimelog type implementation
    src/py_iter.c       # PyTimelogIter type implementation
    src/py_span.c       # PyPageSpan type implementation
    src/py_span_iter.c  # PyPageSpanIter type implementation
    src/py_span_objects.c # PyPageSpanObjectsView type implementation
    src/module.c        # Module initialization
)

# Create Python extension module.
# WITH_SOABI ensures wheel-compatible extension naming.
Python3_add_library(_timelog MODULE WITH_SOABI ${TIMELOG_PY_SOURCES})

# Determine TIMELOG_ROOT for internal headers
if(NOT DEFINED TIMELOG_ROOT)
    set(TIMELOG_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/../..")
endif()
if(NOT DEFINED TIMELOG_PYTHON_PACKAGE_DIR)
    set(TIMELOG_PYTHON_PACKAGE_DIR
        "${TIMELOG_ROOT}/python/timelog"
        CACHE PATH "Directory where built _timelog extension is staged"
    )
endif()

# Include directories
# NOTE: B4 requires access to internal headers in core/src
target_include_directories(_timelog PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/include
    ${Python3_INCLUDE_DIRS}
    ${TIMELOG_ROOT}/core/src  # Internal headers for B4 (tl_page.h, tl_segment.h, etc.)
)

# Link against timelog core library
target_link_libraries(_timelog PRIVATE timelog)

# Compiler settings
if(MSVC)
    target_compile_options(_timelog PRIVATE
        /W4
        /WX-
        /D_CRT_SECURE_NO_WARNINGS
        /std:c17
        /experimental:c11atomics
    )
else()
    target_compile_options(_timelog PRIVATE
        -Wall -Wextra -Wpedantic
        -Wno-unused-parameter
        -fvisibility=hidden
    )
endif()

if(TIMELOG_STAGE_PYTHON_MODULE)
    add_custom_command(TARGET _timelog POST_BUILD
        COMMAND ${CMAKE_COMMAND} -E make_directory "${TIMELOG_PYTHON_PACKAGE_DIR}"
        COMMAND ${CMAKE_COMMAND} -E copy_if_different
                "$<TARGET_FILE:_timelog>"
                "${TIMELOG_PYTHON_PACKAGE_DIR}/$<TARGET_FILE_NAME:_timelog>"
        COMMENT "Staging _timelog in ${TIMELOG_PYTHON_PACKAGE_DIR}"
        VERBATIM
    )

    add_custom_target(stage_timelog_python_module DEPENDS _timelog)
endif()

# =============================================================================
# Test Executable for Handle Context (C-level tests)
# =============================================================================

# Optional: build a test executable for the handle context
# This allows testing the lock-free queue and pin tracking without Python
# (TIMELOG_BUILD_PY_TESTS is declared by the root CMakeLists.txt.)
if(TIMELOG_BUILD_PY_TESTS)
    # Embedded-Python C tests may run under launcher shims (e.g. pyenv) where
    # executable dirname is not a valid CPython home. Resolve a stable prefix
    # once at configure time and pass it to CTest via PYTHONHOME.
    set(TIMELOG_TEST_PYTHONHOME "")
    if(Python3_EXECUTABLE)
        execute_process(
            COMMAND "${Python3_EXECUTABLE}" -c "import sys; print(sys.base_prefix)"
            RESULT_VARIABLE _timelog_pyhome_rc
            OUTPUT_VARIABLE _timelog_pyhome_out
            OUTPUT_STRIP_TRAILING_WHITESPACE
            ERROR_QUIET
        )
        if(_timelog_pyhome_rc EQUAL 0 AND IS_DIRECTORY "${_timelog_pyhome_out}")
            set(TIMELOG_TEST_PYTHONHOME "${_timelog_pyhome_out}")
        elseif(DEFINED Python3_PREFIX AND IS_DIRECTORY "${Python3_PREFIX}")
            set(TIMELOG_TEST_PYTHONHOME "${Python3_PREFIX}")
        endif()
    endif()

    # =========================================================================
    # Test Executables
    # =========================================================================

    # One canonical way to declare an embedded-Python C test executable.
    #   NO_CORE_LINK       link only against Python3 (black-box import tests)
    #   OMIT_CORE_INCLUDES skip TIMELOG_ROOT/core/src (tests without internals)
    function(timelog_add_py_test)
        cmake_parse_arguments(arg
            "NO_CORE_LINK;OMIT_CORE_INCLUDES" "NAME" "SOURCES;EXTRA_DEFS" ${ARGN})

        add_executable(${arg_NAME} ${arg_SOURCES})

        target_include_directories(${arg_NAME} PRIVATE
            ${CMAKE_CURRENT_SOURCE_DIR}/include
            ${Python3_INCLUDE_DIRS}
        )
        if(NOT arg_OMIT_CORE_INCLUDES)
            # Internal headers for B4 (tl_page.h, tl_segment.h, etc.)
            target_include_directories(${arg_NAME} PRIVATE ${TIMELOG_ROOT}/core/src)
        endif()

        if(Python3_EXECUTABLE)
            target_compile_definitions(${arg_NAME} PRIVATE
                TIMELOG_PYTHON_EXECUTABLE=\"${Python3_EXECUTABLE}\"
            )
        endif()
        if(arg_EXTRA_DEFS)
            target_compile_definitions(${arg_NAME} PRIVATE ${arg_EXTRA_DEFS})
        endif()

        if(arg_NO_CORE_LINK)
            target_link_libraries(${arg_NAME} PRIVATE ${Python3_LIBRARIES})
        else()
            target_link_libraries(${arg_NAME} PRIVATE timelog ${Python3_LIBRARIES})
        endif()

        timelog_copy_python_runtime(${arg_NAME})

        if(MSVC)
            target_compile_options(${arg_NAME} PRIVATE
                /W4
                /WX-
                /D_CRT_SECURE_NO_WARNINGS
                /std:c17
                /experimental:c11atomics
            )
        else()
            target_compile_options(${arg_NAME} PRIVATE
                -Wall -Wextra -Wpedantic
                -Wno-unused-parameter
            )
        endif()
    endfunction()

    # Most test executables compile the full extension source set directly
    # into the test binary (white-box testing of module internals).
    set(_timelog_py_test_sources
        src/module.c
        src/py_handle.c
        src/py_errors.c
        src/py_timelog.c
        src/py_iter.c
        src/py_span.c
        src/py_span_iter.c
        src/py_span_objects.c
    )

    timelog_add_py_test(NAME test_py_handle
        SOURCES tests/test_py_handle.c src/py_handle.c
        OMIT_CORE_INCLUDES
    )
    timelog_add_py_test(NAME test_py_timelog
        SOURCES tests/test_py_timelog.c ${_timelog_py_test_sources}
        EXTRA_DEFS TL_PY_MODULE_TEST_HOOKS
    )
    timelog_add_py_test(NAME test_py_iter
        SOURCES tests/test_py_iter.c ${_timelog_py_test_sources}
        EXTRA_DEFS TL_PY_MODULE_TEST_HOOKS TL_PY_ITER_TEST_HOOKS
    )
    timelog_add_py_test(NAME test_py_span
        SOURCES tests/test_py_span.c ${_timelog_py_test_sources}
        EXTRA_DEFS TL_PY_MODULE_TEST_HOOKS
    )
    timelog_add_py_test(NAME test_py_maint_b5
        SOURCES tests/test_py_maint_b5.c ${_timelog_py_test_sources}
        EXTRA_DEFS TL_PY_MODULE_TEST_HOOKS
    )
    timelog_add_py_test(NAME test_py_errors
        SOURCES tests/test_py_errors.c ${_timelog_py_test_sources}
    )
    timelog_add_py_test(NAME test_py_module
        SOURCES tests/test_py_module.c
        NO_CORE_LINK
        OMIT_CORE_INCLUDES
    )
    timelog_add_py_test(NAME test_py_module_exec
        SOURCES tests/test_py_module_exec.c ${_timelog_py_test_sources}
        EXTRA_DEFS TL_PY_MODULE_TEST_HOOKS
    )

    # =========================================================================
    # CTest Integration - Run all tests with 'ctest' command
    # =========================================================================
    enable_testing()

    add_test(NAME py_handle_tests
        COMMAND test_py_handle
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )

    add_test(NAME py_timelog_tests
        COMMAND test_py_timelog
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )

    add_test(NAME py_iter_tests
        COMMAND test_py_iter
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )

    add_test(NAME py_span_tests
        COMMAND test_py_span
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )

    add_test(NAME py_maint_b5_tests
        COMMAND test_py_maint_b5
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )

    add_test(NAME py_errors_tests
        COMMAND test_py_errors
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )

    add_test(NAME py_module_tests
        COMMAND test_py_module
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )

    add_test(NAME py_module_exec_tests
        COMMAND test_py_module_exec
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )

    set(_timelog_py_test_env "")
    if(TIMELOG_TEST_PYTHONHOME)
        list(APPEND _timelog_py_test_env "PYTHONHOME=${TIMELOG_TEST_PYTHONHOME}")
    endif()
    if(NOT WIN32)
        # Embedded CPython may keep tiny process-lifetime allocations that are
        # not actionable for extension correctness; keep ASan/UBSan enabled but
        # disable LSan in these CTest runs to avoid false-red failures.
        list(APPEND _timelog_py_test_env "ASAN_OPTIONS=detect_leaks=0")
    endif()

    if(_timelog_py_test_env)
        set_tests_properties(
            py_handle_tests
            py_timelog_tests
            py_iter_tests
            py_span_tests
            py_maint_b5_tests
            py_errors_tests
            py_module_exec_tests
            PROPERTIES
            ENVIRONMENT "${_timelog_py_test_env}"
        )
    endif()

    set(_timelog_py_module_test_env ${_timelog_py_test_env})
    list(APPEND _timelog_py_module_test_env "PYTHONPATH=${TIMELOG_ROOT}/python")
    set_tests_properties(
        py_module_tests
        PROPERTIES
        ENVIRONMENT "${_timelog_py_module_test_env}"
    )

    # Custom target to run all tests (alternative to ctest)
    # Note: -C $<CONFIG> is required for multi-config generators (MSVC)
    add_custom_target(run_all_tests
        COMMAND ${CMAKE_CTEST_COMMAND} -C $<CONFIG> --output-on-failure
        DEPENDS _timelog test_py_handle test_py_timelog test_py_iter test_py_span test_py_maint_b5 test_py_errors test_py_module test_py_module_exec
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
        COMMENT "Running all CPython binding tests..."
    )
endif()

# =============================================================================
# Installation
# =============================================================================

# Install extension into the wheel/package-relative ``timelog`` package dir.
# scikit-build-core selects components during wheel assembly.

install(TARGETS _timelog
    LIBRARY DESTINATION timelog COMPONENT python
    RUNTIME DESTINATION timelog COMPONENT python
)
