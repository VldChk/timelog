#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "../src/internal/tl_alloc.h"

/* Test macros */
#define TEST_ASSERT(cond) do { \
    if (!(cond)) { \
        fprintf(stderr, "FAIL: %s:%d: %s\n", __FILE__, __LINE__, #cond); \
        return 1; \
    } \
} while(0)

#define TEST_ASSERT_EQ(a, b) TEST_ASSERT((a) == (b))
#define TEST_ASSERT_NE(a, b) TEST_ASSERT((a) != (b))

/* Custom allocator for testing */
static int alloc_count = 0;
static int free_count = 0;

static void* test_malloc(void* ctx, size_t size) {
    (void)ctx;
    alloc_count++;
    return malloc(size);
}

static void* test_calloc(void* ctx, size_t count, size_t size) {
    (void)ctx;
    alloc_count++;
    return calloc(count, size);
}

static void* test_realloc(void* ctx, void* ptr, size_t new_size) {
    (void)ctx;
    return realloc(ptr, new_size);
}

static void test_free(void* ctx, void* ptr) {
    (void)ctx;
    free_count++;
    free(ptr);
}

int test_alloc(void) {
    /* Test default allocator initialization */
    tl_allocator_t alloc;
    tl_allocator_init_default(&alloc);
    TEST_ASSERT_EQ(alloc.ctx, NULL);
    TEST_ASSERT_NE(alloc.malloc_fn, NULL);
    TEST_ASSERT_NE(alloc.calloc_fn, NULL);
    TEST_ASSERT_NE(alloc.realloc_fn, NULL);
    TEST_ASSERT_NE(alloc.free_fn, NULL);

    /* Test allocation with default allocator */
    void* p = tl__malloc(&alloc, 100);
    TEST_ASSERT_NE(p, NULL);
    tl__free(&alloc, p);

    /* Test calloc zeroes memory */
    p = tl__calloc(&alloc, 10, sizeof(int));
    TEST_ASSERT_NE(p, NULL);
    int* ip = (int*)p;
    for (int i = 0; i < 10; i++) {
        TEST_ASSERT_EQ(ip[i], 0);
    }
    tl__free(&alloc, p);

    /* Test realloc */
    p = tl__malloc(&alloc, 50);
    TEST_ASSERT_NE(p, NULL);
    void* p2 = tl__realloc(&alloc, p, 200);
    TEST_ASSERT_NE(p2, NULL);
    tl__free(&alloc, p2);

    /* Test NULL allocator uses libc */
    p = tl__malloc(NULL, 100);
    TEST_ASSERT_NE(p, NULL);
    tl__free(NULL, p);

    /* Test custom allocator */
    tl_allocator_t custom = {
        .ctx = NULL,
        .malloc_fn = test_malloc,
        .calloc_fn = test_calloc,
        .realloc_fn = test_realloc,
        .free_fn = test_free
    };

    alloc_count = 0;
    free_count = 0;

    p = tl__malloc(&custom, 100);
    TEST_ASSERT_NE(p, NULL);
    TEST_ASSERT_EQ(alloc_count, 1);

    tl__free(&custom, p);
    TEST_ASSERT_EQ(free_count, 1);

    p = tl__calloc(&custom, 5, sizeof(int));
    TEST_ASSERT_NE(p, NULL);
    TEST_ASSERT_EQ(alloc_count, 2);

    tl__free(&custom, p);
    TEST_ASSERT_EQ(free_count, 2);

    /* Test aligned allocation */
    p = tl__aligned_alloc(&alloc, 64, 128);
    TEST_ASSERT_NE(p, NULL);
    TEST_ASSERT_EQ(((uintptr_t)p) % 64, 0);  /* Check alignment */
    tl__aligned_free(&alloc, p);

    /* Test aligned allocation with custom allocator */
    p = tl__aligned_alloc(&custom, 32, 100);
    TEST_ASSERT_NE(p, NULL);
    TEST_ASSERT_EQ(((uintptr_t)p) % 32, 0);
    tl__aligned_free(&custom, p);

    /* Test NULL-safe free */
    tl__free(&alloc, NULL);
    tl__aligned_free(&alloc, NULL);

    return 0;
}
