#!/bin/bash
CLANG_TIDY="/c/Program Files/LLVM/bin/clang-tidy"
CHECKS="-*,bugprone-*,clang-analyzer-*,performance-*,readability-const-return-type,readability-non-const-parameter,misc-redundant-expression"
INCLUDES="-std=c17 -Iinclude -Isrc -Isrc/storage -Isrc/delta -Isrc/query -Isrc/maint -D_CRT_SECURE_NO_WARNINGS"

"$CLANG_TIDY" "$1" --checks="$CHECKS" -- $INCLUDES
