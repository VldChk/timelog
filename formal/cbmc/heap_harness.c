#include <stdlib.h>
#include <stdint.h>

#include "../../core/src/internal/tl_heap.h"

extern size_t nondet_size_t(void);
extern uint32_t nondet_u32(void);
extern uint64_t nondet_u64(void);
extern int64_t nondet_i64(void);

void __CPROVER_assume(_Bool);
void __CPROVER_assert(_Bool, const char *);

void* tl__realloc(tl_alloc_ctx_t* ctx, void* ptr, size_t new_size) {
    (void)ctx;
    (void)ptr;
    if (new_size == 0) {
        return NULL;
    }
    return malloc(new_size);
}

void tl__free(tl_alloc_ctx_t* ctx, void* ptr) {
    (void)ctx;
    free(ptr);
}

#include "../../core/src/internal/tl_heap.c"

static int lex_cmp(const tl_heap_entry_t* a, const tl_heap_entry_t* b) {
    if (a->ts < b->ts) return -1;
    if (a->ts > b->ts) return 1;
    if (a->tie_break_key < b->tie_break_key) return -1;
    if (a->tie_break_key > b->tie_break_key) return 1;
    return 0;
}

void harness_heap_ordering_and_tiebreak_stability(void) {
    tl_alloc_ctx_t alloc = {0};
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    size_t n = nondet_size_t();
    __CPROVER_assume(n <= 8);

    for (size_t i = 0; i < n; ++i) {
        tl_heap_entry_t e = {
            .ts = nondet_i64(),
            .tie_break_key = nondet_u32(),
            .handle = nondet_u64(),
            .watermark = nondet_u64(),
            .iter = NULL,
        };
        tl_status_t st = tl_heap_push(&h, &e);
        __CPROVER_assert(st == TL_OK || st == TL_ENOMEM, "push status");
    }

    tl_heap_entry_t prev = {0};
    int have_prev = 0;

    while (h.len > 0) {
        tl_heap_entry_t cur;
        tl_status_t st = tl_heap_pop(&h, &cur);
        __CPROVER_assert(st == TL_OK, "pop succeeds while heap non-empty");

        if (have_prev) {
            __CPROVER_assert(lex_cmp(&prev, &cur) <= 0,
                             "heap pops in non-decreasing (ts, tie_break_key) order");
            if (prev.ts == cur.ts) {
                __CPROVER_assert(prev.tie_break_key <= cur.tie_break_key,
                                 "stable tie-break ordering for equal timestamps");
            }
        }

        prev = cur;
        have_prev = 1;
    }

    tl_heap_destroy(&h);
}
