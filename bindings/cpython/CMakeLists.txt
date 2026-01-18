# =============================================================================
# Timelog Python Bindings (CPython Extension)
# =============================================================================
#
# This CMakeLists.txt can be used in two ways:
# 1. Included from the root timelog CMakeLists.txt via add_subdirectory()
# 2. Built standalone for development/testing
#
# Build (standalone):
#   cmake -B build -DPYTHON_EXECUTABLE=python3
#   cmake --build build
#
# Build (from root):
#   cmake -B build -DTIMELOG_BUILD_PYTHON=ON
#   cmake --build build
#

cmake_minimum_required(VERSION 3.14)

# If building standalone, set up project
if(NOT TARGET timelog)
    project(timelog_python VERSION 1.0.0 LANGUAGES C)

    set(CMAKE_C_STANDARD 17)
    set(CMAKE_C_STANDARD_REQUIRED ON)
    set(CMAKE_C_EXTENSIONS OFF)

    # Need to find parent timelog library
    # Assume it's built in ../.. relative to this file
    set(TIMELOG_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/../..")

    # Import timelog as an interface library pointing to built static lib
    add_library(timelog STATIC IMPORTED)

    # Find the library - check multiple locations for Windows/Unix builds
    if(WIN32)
        # Windows: Check build_x64/Release, build_x64/Debug, build/Release, build/Debug
        if(EXISTS "${TIMELOG_ROOT}/build_x64/Release/timelog.lib")
            set(TIMELOG_LIB_PATH "${TIMELOG_ROOT}/build_x64/Release/timelog.lib")
        elseif(EXISTS "${TIMELOG_ROOT}/build_x64/Debug/timelog.lib")
            set(TIMELOG_LIB_PATH "${TIMELOG_ROOT}/build_x64/Debug/timelog.lib")
        elseif(EXISTS "${TIMELOG_ROOT}/build/Release/timelog.lib")
            set(TIMELOG_LIB_PATH "${TIMELOG_ROOT}/build/Release/timelog.lib")
        elseif(EXISTS "${TIMELOG_ROOT}/build/Debug/timelog.lib")
            set(TIMELOG_LIB_PATH "${TIMELOG_ROOT}/build/Debug/timelog.lib")
        else()
            message(FATAL_ERROR "Cannot find timelog.lib - build core library first")
        endif()
    else()
        # Unix: Check build/libtimelog.a
        if(EXISTS "${TIMELOG_ROOT}/build/libtimelog.a")
            set(TIMELOG_LIB_PATH "${TIMELOG_ROOT}/build/libtimelog.a")
        else()
            message(FATAL_ERROR "Cannot find libtimelog.a - build core library first")
        endif()
    endif()

    set_target_properties(timelog PROPERTIES
        IMPORTED_LOCATION "${TIMELOG_LIB_PATH}"
        INTERFACE_INCLUDE_DIRECTORIES "${TIMELOG_ROOT}/core/include"
    )

    message(STATUS "Standalone build: linking against ${TIMELOG_LIB_PATH}")
endif()

# =============================================================================
# Find Python
# =============================================================================

find_package(Python3 REQUIRED COMPONENTS Interpreter Development)

message(STATUS "Python3 found: ${Python3_EXECUTABLE}")
message(STATUS "Python3 include: ${Python3_INCLUDE_DIRS}")
message(STATUS "Python3 libraries: ${Python3_LIBRARIES}")

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
    src/py_timelog.c    # LLD-B2: PyTimelog type implementation
    src/py_iter.c       # LLD-B3: PyTimelogIter type implementation
    src/py_span.c       # LLD-B4: PyPageSpan type implementation
    src/py_span_iter.c  # LLD-B4: PyPageSpanIter type implementation
    src/py_span_objects.c # LLD-B4: PyPageSpanObjectsView type implementation
    src/module.c        # Module initialization
)

# Create Python extension module
Python3_add_library(_timelog MODULE ${TIMELOG_PY_SOURCES})

# Determine TIMELOG_ROOT for internal headers
if(NOT DEFINED TIMELOG_ROOT)
    set(TIMELOG_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/../..")
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

# =============================================================================
# Test Executable for Handle Context (C-level tests)
# =============================================================================

# Optional: build a test executable for the handle context
# This allows testing the lock-free queue and pin tracking without Python
option(TIMELOG_BUILD_PY_TESTS "Build C-level tests for Python bindings" ON)

if(TIMELOG_BUILD_PY_TESTS)
    # =========================================================================
    # Test: test_py_handle (LLD-B1 unit tests)
    # =========================================================================
    add_executable(test_py_handle
        tests/test_py_handle.c
        src/py_handle.c         # LLD-B1 implementation under test
    )

    target_include_directories(test_py_handle PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${Python3_INCLUDE_DIRS}
    )

    if(Python3_EXECUTABLE)
        target_compile_definitions(test_py_handle PRIVATE
            TIMELOG_PYTHON_EXECUTABLE=\"${Python3_EXECUTABLE}\"
        )
    endif()

    target_link_libraries(test_py_handle PRIVATE
        timelog
        ${Python3_LIBRARIES}
    )

    timelog_copy_python_runtime(test_py_handle)

    if(MSVC)
        target_compile_options(test_py_handle PRIVATE
            /W4
            /D_CRT_SECURE_NO_WARNINGS
            /std:c17
            /experimental:c11atomics
        )
    else()
        target_compile_options(test_py_handle PRIVATE
            -Wall -Wextra -Wpedantic
            -Wno-unused-parameter
        )
        target_link_options(test_py_handle PRIVATE
            -fsanitize=address,undefined
        )
        target_compile_options(test_py_handle PRIVATE
            -fsanitize=address,undefined
        )
    endif()

    # =========================================================================
    # Test: test_py_timelog (LLD-B2 unit tests)
    # =========================================================================
    add_executable(test_py_timelog
        tests/test_py_timelog.c
        src/py_handle.c         # LLD-B1 dependency
        src/py_errors.c         # Error translation
        src/py_timelog.c        # LLD-B2 implementation under test
        src/py_iter.c           # LLD-B3 dependency (used by py_timelog.c)
        src/py_span.c           # LLD-B4 dependency (used by py_timelog.c)
        src/py_span_iter.c      # LLD-B4 dependency
        src/py_span_objects.c   # LLD-B4 dependency
    )

    target_include_directories(test_py_timelog PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${Python3_INCLUDE_DIRS}
        ${TIMELOG_ROOT}/core/src     # Internal headers for B4
    )

    if(Python3_EXECUTABLE)
        target_compile_definitions(test_py_timelog PRIVATE
            TIMELOG_PYTHON_EXECUTABLE=\"${Python3_EXECUTABLE}\"
        )
    endif()

    target_link_libraries(test_py_timelog PRIVATE
        timelog
        ${Python3_LIBRARIES}
    )

    timelog_copy_python_runtime(test_py_timelog)

    if(MSVC)
        target_compile_options(test_py_timelog PRIVATE
            /W4
            /D_CRT_SECURE_NO_WARNINGS
            /std:c17
            /experimental:c11atomics
        )
    else()
        target_compile_options(test_py_timelog PRIVATE
            -Wall -Wextra -Wpedantic
            -Wno-unused-parameter
        )
        target_link_options(test_py_timelog PRIVATE
            -fsanitize=address,undefined
        )
        target_compile_options(test_py_timelog PRIVATE
            -fsanitize=address,undefined
        )
    endif()

    # =========================================================================
    # Test: test_py_iter (LLD-B3 unit tests)
    # =========================================================================
    add_executable(test_py_iter
        tests/test_py_iter.c
        src/py_handle.c         # LLD-B1 dependency
        src/py_errors.c         # Error translation
        src/py_timelog.c        # LLD-B2 dependency (factory methods)
        src/py_iter.c           # LLD-B3 implementation under test
        src/py_span.c           # LLD-B4 dependency (used by py_timelog.c)
        src/py_span_iter.c      # LLD-B4 dependency
        src/py_span_objects.c   # LLD-B4 dependency
    )

    target_include_directories(test_py_iter PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${Python3_INCLUDE_DIRS}
        ${TIMELOG_ROOT}/core/src     # Internal headers for B4
    )

    if(Python3_EXECUTABLE)
        target_compile_definitions(test_py_iter PRIVATE
            TIMELOG_PYTHON_EXECUTABLE=\"${Python3_EXECUTABLE}\"
        )
    endif()

    target_link_libraries(test_py_iter PRIVATE
        timelog
        ${Python3_LIBRARIES}
    )

    timelog_copy_python_runtime(test_py_iter)

    if(MSVC)
        target_compile_options(test_py_iter PRIVATE
            /W4
            /D_CRT_SECURE_NO_WARNINGS
            /std:c17
            /experimental:c11atomics
        )
    else()
        target_compile_options(test_py_iter PRIVATE
            -Wall -Wextra -Wpedantic
            -Wno-unused-parameter
        )
        target_link_options(test_py_iter PRIVATE
            -fsanitize=address,undefined
        )
        target_compile_options(test_py_iter PRIVATE
            -fsanitize=address,undefined
        )
    endif()

    # =========================================================================
    # Test: test_py_span (LLD-B4 unit tests)
    # =========================================================================
    add_executable(test_py_span
        tests/test_py_span.c
        src/py_handle.c         # LLD-B1 dependency
        src/py_errors.c         # Error translation
        src/py_timelog.c        # LLD-B2 dependency (factory methods)
        src/py_iter.c           # LLD-B3 dependency
        src/py_span.c           # LLD-B4 implementation under test
        src/py_span_iter.c      # LLD-B4 iterator
        src/py_span_objects.c   # LLD-B4 objects view
    )

    target_include_directories(test_py_span PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${Python3_INCLUDE_DIRS}
        ${TIMELOG_ROOT}/core/src     # Internal headers for B4
    )

    if(Python3_EXECUTABLE)
        target_compile_definitions(test_py_span PRIVATE
            TIMELOG_PYTHON_EXECUTABLE=\"${Python3_EXECUTABLE}\"
        )
    endif()

    target_link_libraries(test_py_span PRIVATE
        timelog
        ${Python3_LIBRARIES}
    )

    timelog_copy_python_runtime(test_py_span)

    if(MSVC)
        target_compile_options(test_py_span PRIVATE
            /W4
            /D_CRT_SECURE_NO_WARNINGS
            /std:c17
            /experimental:c11atomics
        )
    else()
        target_compile_options(test_py_span PRIVATE
            -Wall -Wextra -Wpedantic
            -Wno-unused-parameter
        )
        target_link_options(test_py_span PRIVATE
            -fsanitize=address,undefined
        )
        target_compile_options(test_py_span PRIVATE
            -fsanitize=address,undefined
        )
    endif()

    # =========================================================================
    # Test: test_py_maint_b5 (LLD-B5 unit tests - Maintenance + Threading)
    # =========================================================================
    add_executable(test_py_maint_b5
        tests/test_py_maint_b5.c
        src/py_handle.c         # LLD-B1 dependency
        src/py_errors.c         # Error translation
        src/py_timelog.c        # LLD-B2 dependency (factory methods)
        src/py_iter.c           # LLD-B3 dependency
        src/py_span.c           # LLD-B4 dependency
        src/py_span_iter.c      # LLD-B4 dependency
        src/py_span_objects.c   # LLD-B4 dependency
    )

    target_include_directories(test_py_maint_b5 PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${Python3_INCLUDE_DIRS}
        ${TIMELOG_ROOT}/core/src     # Internal headers for B4
    )

    if(Python3_EXECUTABLE)
        target_compile_definitions(test_py_maint_b5 PRIVATE
            TIMELOG_PYTHON_EXECUTABLE=\"${Python3_EXECUTABLE}\"
        )
    endif()

    target_link_libraries(test_py_maint_b5 PRIVATE
        timelog
        ${Python3_LIBRARIES}
    )

    timelog_copy_python_runtime(test_py_maint_b5)

    if(MSVC)
        target_compile_options(test_py_maint_b5 PRIVATE
            /W4
            /D_CRT_SECURE_NO_WARNINGS
            /std:c17
            /experimental:c11atomics
        )
    else()
        target_compile_options(test_py_maint_b5 PRIVATE
            -Wall -Wextra -Wpedantic
            -Wno-unused-parameter
        )
        target_link_options(test_py_maint_b5 PRIVATE
            -fsanitize=address,undefined
        )
        target_compile_options(test_py_maint_b5 PRIVATE
            -fsanitize=address,undefined
        )
    endif()

    # =========================================================================
    # Test: test_py_errors (LLD-B6 unit tests - Error Model Subsystem)
    # =========================================================================
    add_executable(test_py_errors
        tests/test_py_errors.c
        src/py_handle.c         # LLD-B1 dependency
        src/py_errors.c         # Error translation (primary target)
        src/py_timelog.c        # LLD-B2 dependency (integration tests)
        src/py_iter.c           # LLD-B3 dependency (integration tests)
        src/py_span.c           # LLD-B4 dependency
        src/py_span_iter.c      # LLD-B4 dependency
        src/py_span_objects.c   # LLD-B4 dependency
    )

    target_include_directories(test_py_errors PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${Python3_INCLUDE_DIRS}
        ${TIMELOG_ROOT}/core/src     # Internal headers
    )

    if(Python3_EXECUTABLE)
        target_compile_definitions(test_py_errors PRIVATE
            TIMELOG_PYTHON_EXECUTABLE=\"${Python3_EXECUTABLE}\"
        )
    endif()

    target_link_libraries(test_py_errors PRIVATE
        timelog
        ${Python3_LIBRARIES}
    )

    timelog_copy_python_runtime(test_py_errors)

    if(MSVC)
        target_compile_options(test_py_errors PRIVATE
            /W4
            /D_CRT_SECURE_NO_WARNINGS
            /std:c17
            /experimental:c11atomics
        )
    else()
        target_compile_options(test_py_errors PRIVATE
            -Wall -Wextra -Wpedantic
            -Wno-unused-parameter
        )
        target_link_options(test_py_errors PRIVATE
            -fsanitize=address,undefined
        )
        target_compile_options(test_py_errors PRIVATE
            -fsanitize=address,undefined
        )
    endif()

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

    # Custom target to run all tests (alternative to ctest)
    # Note: -C $<CONFIG> is required for multi-config generators (MSVC)
    add_custom_target(run_all_tests
        COMMAND ${CMAKE_CTEST_COMMAND} -C $<CONFIG> --output-on-failure
        DEPENDS test_py_handle test_py_timelog test_py_iter test_py_span test_py_maint_b5 test_py_errors
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
        COMMENT "Running all CPython binding tests..."
    )
endif()

# =============================================================================
# Installation
# =============================================================================

# Install the extension module to Python site-packages
# This is typically done via pip/setuptools, not CMake directly
# But we provide the target for manual installation

install(TARGETS _timelog
    LIBRARY DESTINATION "${Python3_SITEARCH}/timelog"
)
