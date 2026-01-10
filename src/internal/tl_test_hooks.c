/*===========================================================================
 * tl_test_hooks.c - Test hook implementations
 *
 * This file contains implementations for test-only hooks that allow
 * intercepting internal behavior for testing purposes.
 *
 * Only compiled when TL_TEST_HOOKS is defined.
 *===========================================================================*/

#include "tl_platform.h"

#ifdef TL_TEST_HOOKS

/*===========================================================================
 * Assert Hook
 *
 * Global hook for intercepting TL_ASSERT without aborting.
 * Used by tests to verify assertion conditions.
 *===========================================================================*/

#ifdef TL_DEBUG

/* Global hook pointer - NULL by default (normal assert behavior) */
tl_assert_hook_fn tl__test_assert_hook = NULL;

void tl__test_set_assert_hook(tl_assert_hook_fn hook) {
    tl__test_assert_hook = hook;
}

#endif /* TL_DEBUG */

#endif /* TL_TEST_HOOKS */
