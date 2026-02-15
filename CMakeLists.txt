cmake_minimum_required(VERSION 3.14)
project(timelog VERSION 1.0.0 LANGUAGES C)

# =============================================================================
# Build Configuration
# =============================================================================

set(CMAKE_C_STANDARD 17)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

# Option for native architecture optimizations (off by default for portability)
option(TIMELOG_NATIVE_OPT "Enable -march=native for maximum local performance" OFF)
# Option to build shared library (exports symbols)
option(TIMELOG_BUILD_SHARED "Build timelog as a shared library" OFF)
option(TIMELOG_BUILD_PYTHON "Build CPython bindings from the top-level build" ON)
option(TIMELOG_BUILD_PY_TESTS "Build C-level tests for Python bindings" ON)
option(TIMELOG_STAGE_PYTHON_MODULE
    "Copy built _timelog extension into python/timelog for in-repo imports" ON)
option(TIMELOG_BUILD_PY_FACADE_TESTS
    "Add target to run python/tests via pytest (requires pytest installed)" OFF)

# Build type defaults to Release
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type" FORCE)
endif()

# =============================================================================
# Compiler Flags
# =============================================================================

if(MSVC)
    # MSVC flags
    add_compile_options(
        /W4                     # Warning level 4
        /WX                     # Warnings as errors
        /wd4100                 # Unreferenced formal parameter (allow)
        /wd4189                 # Local variable initialized but not referenced
        /wd4200                 # Zero-sized array (flexible array member)
        /D_CRT_SECURE_NO_WARNINGS
    )

    # Release optimizations
    set(CMAKE_C_FLAGS_RELEASE "/O2 /Ob2 /DNDEBUG /GL")
    set(CMAKE_EXE_LINKER_FLAGS_RELEASE "/LTCG")
    set(CMAKE_STATIC_LINKER_FLAGS_RELEASE "/LTCG")

    # Debug flags
    set(CMAKE_C_FLAGS_DEBUG "/Od /Zi /RTC1 /DTL_DEBUG=1")

else()
    # GCC/Clang flags
    add_compile_options(
        -Wall -Wextra -Wpedantic
        -Werror
        -Wno-unused-parameter
        -fvisibility=hidden
    )

    # Enable POSIX APIs (clock_gettime, pthread_condattr_setclock, nanosleep, etc.)
    # _POSIX_C_SOURCE=200809L enables POSIX.1-2008 features
    add_compile_definitions(_POSIX_C_SOURCE=200809L)

    # Release optimizations
    set(CMAKE_C_FLAGS_RELEASE "-O3 -DNDEBUG -flto")

    # Optional native architecture tuning
    if(TIMELOG_NATIVE_OPT)
        set(CMAKE_C_FLAGS_RELEASE "${CMAKE_C_FLAGS_RELEASE} -march=native")
    endif()

    # Debug flags
    set(CMAKE_C_FLAGS_DEBUG "-O0 -g3 -DTL_DEBUG=1 -fsanitize=address,undefined")
    set(CMAKE_EXE_LINKER_FLAGS_DEBUG "-fsanitize=address,undefined")
endif()

# =============================================================================
# Library Target
# =============================================================================

set(TIMELOG_SOURCES
    # Phase 0
    core/src/internal/tl_alloc.c
    core/src/internal/tl_log.c
    core/src/tl_timelog.c
    # Phase 1
    core/src/internal/tl_sync.c
    core/src/internal/tl_test_hooks.c
    # Phase 2
    core/src/internal/tl_recvec.c
    core/src/internal/tl_seqvec.c
    core/src/internal/tl_intervals.c
    core/src/internal/tl_heap.c
    # Phase 3
    core/src/storage/tl_window.c
    core/src/storage/tl_page.c
    core/src/storage/tl_segment.c
    core/src/storage/tl_manifest.c
    # Phase 4
    core/src/delta/tl_memrun.c
    core/src/delta/tl_ooorun.c
    core/src/delta/tl_memtable.c
    core/src/delta/tl_flush.c
    # Phase 5
    core/src/delta/tl_memview.c
    core/src/query/tl_snapshot.c
    core/src/query/tl_segment_iter.c
    core/src/query/tl_memrun_iter.c
    core/src/query/tl_active_iter.c
    core/src/query/tl_iter_build.c
    core/src/query/tl_submerge.c
    core/src/query/tl_plan.c
    core/src/query/tl_merge_iter.c
    core/src/query/tl_filter.c
    core/src/query/tl_point.c
    core/src/query/tl_pagespan_iter.c
    # Phase 8
    core/src/maint/tl_compaction.c
    # Adaptive Segmentation (V-Next)
    core/src/maint/tl_adaptive.c
)

if(TIMELOG_BUILD_SHARED)
    set(TIMELOG_LIB_TYPE SHARED)
else()
    set(TIMELOG_LIB_TYPE STATIC)
endif()

add_library(timelog ${TIMELOG_LIB_TYPE} ${TIMELOG_SOURCES})

target_include_directories(timelog
    PUBLIC  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/core/include>
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/core/src
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/core/src/storage
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/core/src/delta
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/core/src/query
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/core/src/maint
)

# Enable test hooks for deterministic failpoint testing (Phase 9)
# This exposes tl_test_force_ebusy_count in tl_compaction.c
target_compile_definitions(timelog PRIVATE TL_TEST_HOOKS)

# Export/import macros for shared builds
if(TIMELOG_BUILD_SHARED)
    target_compile_definitions(timelog
        PUBLIC  TL_BUILD_SHARED
        PRIVATE TL_EXPORTS
    )
endif()

# Link pthread on POSIX systems
if(NOT WIN32)
    find_package(Threads REQUIRED)
    # Adaptive code uses llround; export libm so all timelog consumers link cleanly on Unix.
    target_link_libraries(timelog PUBLIC m)
    target_link_libraries(timelog PRIVATE Threads::Threads)
endif()

# =============================================================================
# Test Target
# =============================================================================

enable_testing()

# Test files organized by category
set(TEST_SOURCES
    core/tests/test_main.c
    # Internal implementation tests (LLD-driven)
    core/tests/test_internal_sync.c
    core/tests/test_internal_data_structures.c
    core/tests/test_storage_internal.c
    core/tests/test_delta_internal.c
    core/tests/test_compaction_internal.c
    # Functional tests (public API behavior)
    core/tests/test_functional.c
    core/tests/test_api_semantics.c
    core/tests/test_snapshot_lifetime.c
    core/tests/test_invariants.c
    # Concurrency and stress tests
    core/tests/test_concurrency.c
    core/tests/test_stress.c
    # PageSpan core API tests
    core/tests/test_pagespan_iter.c
    # Adaptive Segmentation tests
    core/tests/test_adaptive_internal.c
)

add_executable(test_timelog ${TEST_SOURCES})
target_link_libraries(test_timelog PRIVATE timelog)
target_include_directories(test_timelog
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/core/src
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/core/src/storage
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/core/src/delta
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/core/src/query
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/core/src/maint
)

# Clang on Windows (non-MSVC driver) does not pull CRT libs by default.
if (WIN32 AND CMAKE_C_COMPILER_ID STREQUAL "Clang" AND NOT MSVC)
    target_link_libraries(test_timelog PRIVATE
        $<$<CONFIG:Debug>:msvcrtd.lib vcruntimed.lib ucrtd.lib legacy_stdio_definitions.lib oldnames.lib>
        $<$<NOT:$<CONFIG:Debug>>:msvcrt.lib vcruntime.lib ucrt.lib legacy_stdio_definitions.lib oldnames.lib>
    )
endif()

# Enable test hooks for deterministic failpoint testing (Phase 9)
target_compile_definitions(test_timelog PRIVATE TL_TEST_HOOKS)

# Enable adaptive module internal test helpers
target_compile_definitions(test_timelog PRIVATE TL_ADAPTIVE_INTERNAL_TEST)

# Link pthread on POSIX systems
if(NOT WIN32)
    target_link_libraries(test_timelog PRIVATE Threads::Threads)
endif()

add_test(NAME timelog_tests COMMAND test_timelog)

# =============================================================================
# Demo Targets
# =============================================================================

add_executable(adaptive_segmentation_demo demo/adaptive_segmentation_demo.c)
target_link_libraries(adaptive_segmentation_demo PRIVATE timelog)

# =============================================================================
# Python Bindings (Integrated Build)
# =============================================================================

if(TIMELOG_BUILD_PYTHON)
    # Expose repository root for bindings/cpython standalone-aware CMake.
    set(TIMELOG_ROOT "${CMAKE_CURRENT_SOURCE_DIR}")
    if(NOT DEFINED TIMELOG_PYTHON_PACKAGE_DIR)
        set(TIMELOG_PYTHON_PACKAGE_DIR
            "${CMAKE_CURRENT_SOURCE_DIR}/python/timelog"
            CACHE PATH "Directory where built _timelog extension is staged"
        )
    endif()

    add_subdirectory(bindings/cpython)

    add_custom_target(timelog_e2e_build
        DEPENDS timelog test_timelog _timelog
        COMMENT "Build core library/tests plus CPython extension"
    )

    if(TIMELOG_BUILD_PY_TESTS)
        add_dependencies(timelog_e2e_build
            test_py_handle
            test_py_timelog
            test_py_iter
            test_py_span
            test_py_maint_b5
            test_py_errors
        )
    endif()

    add_custom_target(timelog_e2e_test
        COMMAND ${CMAKE_CTEST_COMMAND} -C $<CONFIG> --output-on-failure
        DEPENDS timelog_e2e_build
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
        COMMENT "Run all registered core and binding tests"
    )

    if(TIMELOG_BUILD_PY_FACADE_TESTS)
        add_custom_target(timelog_python_facade_tests
            COMMAND ${CMAKE_COMMAND} -E env
                    "PYTHONPATH=${CMAKE_CURRENT_SOURCE_DIR}/python"
                    "${Python3_EXECUTABLE}" -m pytest
                    "${CMAKE_CURRENT_SOURCE_DIR}/python/tests" -q
            DEPENDS _timelog
            WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
            COMMENT "Run Python facade tests with staged extension module"
        )
    endif()
endif()

# Ensure ASan runtime DLL is discoverable when using Clang on Windows.
if (WIN32 AND CMAKE_C_COMPILER_ID STREQUAL "Clang" AND NOT MSVC)
    execute_process(
        COMMAND ${CMAKE_C_COMPILER} --print-resource-dir
        OUTPUT_VARIABLE _clang_res_dir
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )

    if (_clang_res_dir)
        get_filename_component(_clang_ver "${_clang_res_dir}" NAME)
        get_filename_component(_clang_lib_dir "${_clang_res_dir}" DIRECTORY)
        get_filename_component(_clang_lib_root "${_clang_lib_dir}" DIRECTORY)
        get_filename_component(_clang_root "${_clang_lib_root}" DIRECTORY)

        set(_clang_rt_dir "${_clang_res_dir}/lib/windows")

        if (CMAKE_SIZEOF_VOID_P EQUAL 8)
            set(_clang_rt_dir_alt "${_clang_root}/x64/lib/clang/${_clang_ver}/lib/windows")
            if (EXISTS "${_clang_rt_dir_alt}/clang_rt.asan_dynamic-x86_64.dll")
                set(_clang_rt_dir "${_clang_rt_dir_alt}")
            endif()
        endif()

        set_tests_properties(timelog_tests PROPERTIES
            ENVIRONMENT "PATH=${_clang_rt_dir};$ENV{PATH}"
        )
    endif()
endif()

# =============================================================================
# Installation (optional)
# =============================================================================

install(TARGETS timelog
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
)

install(DIRECTORY core/include/timelog DESTINATION include)
