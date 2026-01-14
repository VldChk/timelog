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
        INTERFACE_INCLUDE_DIRECTORIES "${TIMELOG_ROOT}/include"
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

# =============================================================================
# Python Extension Module: _timelog
# =============================================================================

set(TIMELOG_PY_SOURCES
    src/py_handle.c
    src/py_errors.c
    src/py_timelog.c    # LLD-B2: PyTimelog type implementation
    src/py_iter.c       # LLD-B3: PyTimelogIter type implementation
    src/module.c        # Module initialization
)

# Create Python extension module
Python3_add_library(_timelog MODULE ${TIMELOG_PY_SOURCES})

# Include directories
target_include_directories(_timelog PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/include
    ${Python3_INCLUDE_DIRS}
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

    target_link_libraries(test_py_handle PRIVATE
        timelog
        ${Python3_LIBRARIES}
    )

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
    )

    target_include_directories(test_py_timelog PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${Python3_INCLUDE_DIRS}
    )

    target_link_libraries(test_py_timelog PRIVATE
        timelog
        ${Python3_LIBRARIES}
    )

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
    )

    target_include_directories(test_py_iter PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${Python3_INCLUDE_DIRS}
    )

    target_link_libraries(test_py_iter PRIVATE
        timelog
        ${Python3_LIBRARIES}
    )

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
