@echo off
setlocal

set "CLANG_TIDY=C:\Program Files\LLVM\bin\clang-tidy.exe"
set "CHECKS=-*,bugprone-*,clang-analyzer-*,performance-*,readability-const-return-type,readability-non-const-parameter,misc-redundant-expression"

echo Running clang-tidy on all source files...

for %%f in (
    src\tl_timelog.c
    src\internal\tl_alloc.c
    src\internal\tl_log.c
    src\internal\tl_sync.c
    src\internal\tl_recvec.c
    src\internal\tl_intervals.c
    src\internal\tl_heap.c
    src\storage\tl_window.c
    src\storage\tl_page.c
    src\storage\tl_segment.c
    src\storage\tl_manifest.c
    src\delta\tl_memrun.c
    src\delta\tl_memtable.c
    src\delta\tl_flush.c
    src\delta\tl_memview.c
    src\query\tl_snapshot.c
    src\query\tl_segment_iter.c
    src\query\tl_memrun_iter.c
    src\query\tl_active_iter.c
    src\query\tl_plan.c
    src\query\tl_merge_iter.c
    src\query\tl_filter.c
    src\query\tl_point.c
    src\maint\tl_compaction.c
) do (
    echo.
    echo === Analyzing %%f ===
    "%CLANG_TIDY%" %%f --checks=%CHECKS% -- -std=c17 -Iinclude -Isrc -Isrc/storage -Isrc/delta -Isrc/query -Isrc/maint -D_CRT_SECURE_NO_WARNINGS
)

echo.
echo Done!
endlocal
