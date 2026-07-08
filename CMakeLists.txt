cmake_minimum_required(VERSION 3.15)
project(timelog VERSION 1.3.0 LANGUAGES C)

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
option(TIMELOG_STRICT_WARNINGS
    "Treat compiler warnings as errors for core targets" ON)
option(TIMELOG_BUILD_CORE_TESTS
    "Build core C test executable and register core CTest entry" ON)
option(TIMELOG_BUILD_DEMOS "Build demo executables" ON)
set(TIMELOG_SANITIZER "address-undefined" CACHE STRING
    "Sanitizer set for non-MSVC Debug builds: address-undefined, thread, or none")
set_property(CACHE TIMELOG_SANITIZER PROPERTY STRINGS
    address-undefined thread none)

# Build type defaults to Release
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type" FORCE)
endif()

# =============================================================================
# Compiler Flags
# =============================================================================

if(MSVC)
    # MSVC flags
    set(_timelog_msvc_warn_flags /W4)
    if(TIMELOG_STRICT_WARNINGS)
        list(APPEND _timelog_msvc_warn_flags /WX)
    endif()

    add_compile_options(
        ${_timelog_msvc_warn_flags}
        /wd4100                 # Unreferenced formal parameter (allow)
        /wd4127                 # Conditional expression is constant (assert macros, while(1))
        /wd4189                 # Local variable initialized but not referenced
        /wd4200                 # Zero-sized array (flexible array member)
        /experimental:c11atomics # <stdatomic.h> backend for tl_atomic.h (D1);
                                 # the Windows wheel has required this flag for
                                 # the binding since v1.0.0 (VS2022 17.5+ floor)
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
    set(_timelog_gcc_warn_flags
        -Wall -Wextra -Wpedantic
        -Wno-unused-parameter
        -fvisibility=hidden
    )
    if(TIMELOG_STRICT_WARNINGS)
        list(APPEND _timelog_gcc_warn_flags -Werror)
    endif()
    if(TIMELOG_SANITIZER STREQUAL "thread" AND
       CMAKE_C_COMPILER_ID STREQUAL "GNU")
        # GCC reports C11 fences as unsupported by TSan. Keep the diagnostic
        # visible without making the advisory TSan build uncompilable.
        list(APPEND _timelog_gcc_warn_flags -Wno-error=tsan)
    endif()

    add_compile_options(
        ${_timelog_gcc_warn_flags}
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
    set(CMAKE_C_FLAGS_DEBUG "-O0 -g3 -DTL_DEBUG=1")
    if(TIMELOG_SANITIZER STREQUAL "address-undefined")
        set(_timelog_sanitizer_flags "-fsanitize=address,undefined")
    elseif(TIMELOG_SANITIZER STREQUAL "thread")
        set(_timelog_sanitizer_flags "-fsanitize=thread")
    elseif(TIMELOG_SANITIZER STREQUAL "none")
        set(_timelog_sanitizer_flags "")
    else()
        message(FATAL_ERROR
            "Unsupported TIMELOG_SANITIZER='${TIMELOG_SANITIZER}'. "
            "Use address-undefined, thread, or none.")
    endif()

    if(NOT _timelog_sanitizer_flags STREQUAL "")
        set(_timelog_sanitizer_build_types Debug)
        if(TIMELOG_SANITIZER STREQUAL "thread")
            # The free-threaded TSan CI leg uses RelWithDebInfo to keep runtime
            # manageable. Apply TSan there as well so the job cannot silently
            # produce an uninstrumented "TSan" build.
            list(APPEND _timelog_sanitizer_build_types RelWithDebInfo)
        endif()

        foreach(_timelog_sanitizer_build_type IN LISTS _timelog_sanitizer_build_types)
            string(TOUPPER "${_timelog_sanitizer_build_type}" _timelog_sanitizer_build_type_upper)
            set(CMAKE_C_FLAGS_${_timelog_sanitizer_build_type_upper}
                "${CMAKE_C_FLAGS_${_timelog_sanitizer_build_type_upper}} ${_timelog_sanitizer_flags}")
            set(CMAKE_EXE_LINKER_FLAGS_${_timelog_sanitizer_build_type_upper}
                "${CMAKE_EXE_LINKER_FLAGS_${_timelog_sanitizer_build_type_upper}} ${_timelog_sanitizer_flags}")
            set(CMAKE_SHARED_LINKER_FLAGS_${_timelog_sanitizer_build_type_upper}
                "${CMAKE_SHARED_LINKER_FLAGS_${_timelog_sanitizer_build_type_upper}} ${_timelog_sanitizer_flags}")
            set(CMAKE_MODULE_LINKER_FLAGS_${_timelog_sanitizer_build_type_upper}
                "${CMAKE_MODULE_LINKER_FLAGS_${_timelog_sanitizer_build_type_upper}} ${_timelog_sanitizer_flags}")
        endforeach()

    endif()
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
    core/src/query/tl_delta_iter.c
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
set_target_properties(timelog PROPERTIES POSITION_INDEPENDENT_CODE ON)

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

if(TIMELOG_BUILD_CORE_TESTS)
    # Test files organized by category
    set(TEST_SOURCES
        core/tests/test_main.c
        # Internal implementation tests (LLD-driven)
        core/tests/test_internal_sync.c
        core/tests/test_internal_data_structures.c
        core/tests/test_storage_internal.c
        core/tests/test_search_branchless.c
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

    # Enable test hooks for deterministic failpoint testing (Phase 9)
    target_compile_definitions(test_timelog PRIVATE TL_TEST_HOOKS)

    # Enable adaptive module internal test helpers
    target_compile_definitions(test_timelog PRIVATE TL_ADAPTIVE_INTERNAL_TEST)

    # Link pthread on POSIX systems
    if(NOT WIN32)
        target_link_libraries(test_timelog PRIVATE Threads::Threads)
    endif()

    add_test(NAME timelog_tests COMMAND test_timelog)

    # Per-group CTest entries (CI runs `ctest -L core_group -j <n>`).
    # Group names MUST match the k_test_suites[] table in
    # core/tests/test_main.c; test_timelog exits nonzero when
    # TL_TEST_GROUPS names an unknown group, so drift fails loudly.
    set(TIMELOG_TEST_GROUPS
        internal_sync internal_data storage delta compaction pagespan
        adaptive functional api_semantics snapshot_lifetime invariants
        concurrency stress
    )
    foreach(_tl_group IN LISTS TIMELOG_TEST_GROUPS)
        add_test(NAME core_group_${_tl_group} COMMAND test_timelog)
        set_tests_properties(core_group_${_tl_group} PROPERTIES
            ENVIRONMENT "TL_TEST_GROUPS=${_tl_group}"
            LABELS core_group
            TIMEOUT 600
        )
    endforeach()

    # Bidirectional drift guard: fails if this list and test_main.c's
    # k_test_suites table ever disagree in either direction.
    string(REPLACE ";" "," _tl_groups_csv "${TIMELOG_TEST_GROUPS}")
    add_test(NAME core_group_sync COMMAND test_timelog)
    set_tests_properties(core_group_sync PROPERTIES
        ENVIRONMENT "TL_TEST_EXPECT_GROUPS=${_tl_groups_csv}"
        LABELS core_group
        TIMEOUT 60
    )

    add_executable(bench_search_lower_bound EXCLUDE_FROM_ALL
        core/tests/bench_search_lower_bound.c
    )
    target_link_libraries(bench_search_lower_bound PRIVATE timelog)
    target_include_directories(bench_search_lower_bound
        PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/core/src
    )
endif()

# =============================================================================
# Demo Targets
# =============================================================================

if(TIMELOG_BUILD_DEMOS)
    add_executable(adaptive_segmentation_demo demo/adaptive_segmentation_demo.c)
    target_link_libraries(adaptive_segmentation_demo PRIVATE timelog)

    add_executable(timelog_native_benchmark demo/timelog_native_benchmark.c)
    target_link_libraries(timelog_native_benchmark PRIVATE timelog)

endif()

# =============================================================================
# Python Bindings (Integrated Build)
# =============================================================================

if(TIMELOG_BUILD_PYTHON)
    # Expose repository root to the bindings/cpython subdirectory.
    set(TIMELOG_ROOT "${CMAKE_CURRENT_SOURCE_DIR}")
    if(NOT DEFINED TIMELOG_PYTHON_PACKAGE_DIR)
        set(TIMELOG_PYTHON_PACKAGE_DIR
            "${CMAKE_CURRENT_SOURCE_DIR}/python/timelog"
            CACHE PATH "Directory where built _timelog extension is staged"
        )
    endif()

    add_subdirectory(bindings/cpython)

    set(_timelog_e2e_build_deps timelog _timelog)
    if(TIMELOG_BUILD_CORE_TESTS)
        list(APPEND _timelog_e2e_build_deps test_timelog)
    endif()

    if(TIMELOG_BUILD_PY_TESTS)
        list(APPEND _timelog_e2e_build_deps
            test_py_handle
            test_py_timelog
            test_py_iter
            test_py_span
            test_py_maint_b5
            test_py_errors
            test_py_module
            test_py_module_exec
        )
    endif()

    add_custom_target(timelog_e2e_build
        DEPENDS ${_timelog_e2e_build_deps}
        COMMENT "Build core library/tests plus CPython extension"
    )

    add_custom_target(timelog_e2e_test
        COMMAND ${CMAKE_CTEST_COMMAND} -C $<CONFIG> --output-on-failure
        DEPENDS timelog_e2e_build
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
        COMMENT "Run all registered core and binding tests"
    )
endif()

# =============================================================================
# Installation (optional)
# =============================================================================

install(TARGETS timelog
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
    COMPONENT core
)

install(DIRECTORY core/include/timelog DESTINATION include COMPONENT core)
