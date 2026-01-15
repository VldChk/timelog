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
    src/internal/tl_alloc.c
    src/internal/tl_log.c
    src/tl_timelog.c
    # Phase 1
    src/internal/tl_sync.c
    src/internal/tl_test_hooks.c
    # Phase 2
    src/internal/tl_recvec.c
    src/internal/tl_intervals.c
    src/internal/tl_heap.c
    # Phase 3
    src/storage/tl_window.c
    src/storage/tl_page.c
    src/storage/tl_segment.c
    src/storage/tl_manifest.c
    # Phase 4
    src/delta/tl_memrun.c
    src/delta/tl_memtable.c
    src/delta/tl_flush.c
    # Phase 5
    src/delta/tl_memview.c
    src/query/tl_snapshot.c
    src/query/tl_segment_iter.c
    src/query/tl_memrun_iter.c
    src/query/tl_active_iter.c
    src/query/tl_plan.c
    src/query/tl_merge_iter.c
    src/query/tl_filter.c
    src/query/tl_point.c
    src/query/tl_pagespan_iter.c
    # Phase 8
    src/maint/tl_compaction.c
)

if(TIMELOG_BUILD_SHARED)
    set(TIMELOG_LIB_TYPE SHARED)
else()
    set(TIMELOG_LIB_TYPE STATIC)
endif()

add_library(timelog ${TIMELOG_LIB_TYPE} ${TIMELOG_SOURCES})

target_include_directories(timelog
    PUBLIC  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src/storage
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src/delta
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src/query
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src/maint
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
    target_link_libraries(timelog PRIVATE Threads::Threads)
endif()

# =============================================================================
# Test Target
# =============================================================================

enable_testing()

# Test files organized by category
set(TEST_SOURCES
    tests/test_main.c
    # Internal implementation tests (LLD-driven)
    tests/test_internal_sync.c
    tests/test_internal_data_structures.c
    tests/test_storage_internal.c
    tests/test_delta_internal.c
    tests/test_compaction_internal.c
    # Functional tests (public API behavior)
    tests/test_functional.c
    tests/test_api_semantics.c
    tests/test_snapshot_lifetime.c
    tests/test_invariants.c
    # Concurrency and stress tests
    tests/test_concurrency.c
    tests/test_stress.c
    # PageSpan core API tests
    tests/test_pagespan_iter.c
)

add_executable(test_timelog ${TEST_SOURCES})
target_link_libraries(test_timelog PRIVATE timelog)
target_include_directories(test_timelog
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src/storage
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src/delta
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src/query
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src/maint
)

# Enable test hooks for deterministic failpoint testing (Phase 9)
target_compile_definitions(test_timelog PRIVATE TL_TEST_HOOKS)

# Link pthread on POSIX systems
if(NOT WIN32)
    target_link_libraries(test_timelog PRIVATE Threads::Threads)
endif()

add_test(NAME timelog_tests COMMAND test_timelog)

# =============================================================================
# Installation (optional)
# =============================================================================

install(TARGETS timelog
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
)

install(DIRECTORY include/timelog DESTINATION include)
