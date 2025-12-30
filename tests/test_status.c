#include <stdio.h>
#include "../src/internal/tl_status.h"

/* Test macros */
#define TEST_ASSERT(cond) do { \
    if (!(cond)) { \
        fprintf(stderr, "FAIL: %s:%d: %s\n", __FILE__, __LINE__, #cond); \
        return 1; \
    } \
} while(0)

#define TEST_ASSERT_EQ(a, b) TEST_ASSERT((a) == (b))
#define TEST_ASSERT_NE(a, b) TEST_ASSERT((a) != (b))

int test_status(void) {
    /* Test that TL_OK is zero (for if(status) idiom) */
    TEST_ASSERT_EQ(TL_OK, 0);

    /* Test all status codes have non-NULL strings */
    TEST_ASSERT_NE(tl_strerror(TL_OK), NULL);
    TEST_ASSERT_NE(tl_strerror(TL_EOF), NULL);
    TEST_ASSERT_NE(tl_strerror(TL_EINVAL), NULL);
    TEST_ASSERT_NE(tl_strerror(TL_ESTATE), NULL);
    TEST_ASSERT_NE(tl_strerror(TL_EBUSY), NULL);
    TEST_ASSERT_NE(tl_strerror(TL_ENOMEM), NULL);
    TEST_ASSERT_NE(tl_strerror(TL_EINTERNAL), NULL);

    /* Test that strings are descriptive (not empty) */
    const char* ok_str = tl_strerror(TL_OK);
    TEST_ASSERT(ok_str[0] != '\0');

    /* Test unknown status returns something */
    TEST_ASSERT_NE(tl_strerror((tl_status_t)999), NULL);

    return 0;
}
