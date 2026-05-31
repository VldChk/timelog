#ifndef TL_PLATFORM_H
#define TL_PLATFORM_H

/*===========================================================================
 * Platform Detection
 *===========================================================================*/

#if defined(_WIN32) || defined(_WIN64)
    #define TL_PLATFORM_WINDOWS 1
#elif defined(__linux__)
    #define TL_PLATFORM_LINUX 1
#elif defined(__APPLE__)
    #define TL_PLATFORM_MACOS 1
#else
    #define TL_PLATFORM_UNKNOWN 1
#endif

/*===========================================================================
 * Compiler Detection
 *===========================================================================*/

#if defined(_MSC_VER)
    #define TL_COMPILER_MSVC 1
    #define TL_MSVC_VERSION _MSC_VER
#elif defined(__clang__)
    #define TL_COMPILER_CLANG 1
#elif defined(__GNUC__)
    #define TL_COMPILER_GCC 1
#endif

/*===========================================================================
 * Function Attributes
 *===========================================================================*/

#if defined(TL_COMPILER_MSVC)
    #if defined(__clang__)
        #define TL_INLINE        static inline __attribute__((always_inline))
    #else
        #define TL_INLINE        static __forceinline
    #endif
    #define TL_NOINLINE      __declspec(noinline)
    #define TL_RESTRICT      __restrict
    #define TL_LIKELY(x)     (x)
    #define TL_UNLIKELY(x)   (x)
    #define TL_ALIGNED(n)    __declspec(align(n))
    #define TL_ASSUME(x)     __assume(x)
    #define TL_UNREACHABLE() __assume(0)
    #define TL_THREAD_LOCAL  __declspec(thread)
#else
    #define TL_INLINE        static inline __attribute__((always_inline))
    #define TL_NOINLINE      __attribute__((noinline))
    #define TL_RESTRICT      __restrict__
    #define TL_LIKELY(x)     __builtin_expect(!!(x), 1)
    #define TL_UNLIKELY(x)   __builtin_expect(!!(x), 0)
    #define TL_ALIGNED(n)    __attribute__((aligned(n)))
    #define TL_ASSUME(x)     do { if (!(x)) __builtin_unreachable(); } while(0)
    #define TL_UNREACHABLE() __builtin_unreachable()
    #define TL_THREAD_LOCAL  _Thread_local
#endif

/*===========================================================================
 * Cache Line Size
 *===========================================================================*/

#ifndef TL_CACHE_LINE_SIZE
    #define TL_CACHE_LINE_SIZE 64
#endif

#define TL_CACHE_ALIGNED TL_ALIGNED(TL_CACHE_LINE_SIZE)

/*===========================================================================
 * Debug Assertions
 *
 * TL_ASSERT collapses to TL_ASSUME in release builds, so a violated
 * condition produces undefined behaviour rather than a crash. Use it only
 * for invariants that are true by construction inside timelog itself.
 *
 * Caller-supplied data (API inputs, external state) MUST be validated with
 * explicit branches returning TL_EINVAL — never with TL_ASSERT, because the
 * release-build TL_ASSUME would let the compiler optimise the check away
 * and miscompile downstream code on bad input.
 *===========================================================================*/

#ifdef TL_DEBUG
    #include <assert.h>
    #include <stdio.h>
    #include <stdlib.h>

    #ifdef TL_TEST_HOOKS
        /*
         * Pluggable assertion handler used by the test harness to verify
         * that specific code paths assert without crashing the test runner.
         * When tl__test_assert_hook is non-NULL it is invoked in place of
         * the usual abort(). Typical usage:
         *
         *     tl__test_set_assert_hook(my_hook);
         *     // run code expected to assert
         *     tl__test_set_assert_hook(NULL);
         */
        typedef void (*tl_assert_hook_fn)(const char* file, int line, const char* expr);
        extern tl_assert_hook_fn tl__test_assert_hook;
        void tl__test_set_assert_hook(tl_assert_hook_fn hook);

        #define TL_ASSERT(cond) \
            do { \
                if (!(cond)) { \
                    if (tl__test_assert_hook) { \
                        tl__test_assert_hook(__FILE__, __LINE__, #cond); \
                    } else { \
                        fprintf(stderr, "ASSERT FAILED: %s at %s:%d\n", \
                                #cond, __FILE__, __LINE__); \
                        abort(); \
                    } \
                } \
            } while(0)

        #define TL_ASSERT_MSG(cond, msg) \
            do { \
                if (!(cond)) { \
                    if (tl__test_assert_hook) { \
                        tl__test_assert_hook(__FILE__, __LINE__, #cond ": " msg); \
                    } else { \
                        fprintf(stderr, "ASSERT FAILED: %s (%s) at %s:%d\n", \
                                #cond, msg, __FILE__, __LINE__); \
                        abort(); \
                    } \
                } \
            } while(0)
    #else
        #define TL_ASSERT(cond) assert(cond)
        #define TL_ASSERT_MSG(cond, msg) assert((cond) && (msg))
    #endif /* TL_TEST_HOOKS */
#else
    #define TL_ASSERT(cond) TL_ASSUME(cond)
    #define TL_ASSERT_MSG(cond, msg) TL_ASSUME(cond)
#endif

/*===========================================================================
 * TL_VERIFY: always-on runtime verification.
 *
 * Behaves like TL_ASSERT in debug builds, but in release builds it still
 * evaluates the condition and calls abort() on failure rather than
 * collapsing to TL_ASSUME. Use it for conditions where treating failure as
 * unreachable would be unsafe — typically OS primitive return values
 * (pthread_mutex_lock and friends) and any check whose violation implies
 * system or kernel corruption.
 *===========================================================================*/

#ifdef TL_DEBUG
    #define TL_VERIFY(cond) TL_ASSERT(cond)
#else
    #include <stdlib.h>
    #define TL_VERIFY(cond) do { if (!(cond)) abort(); } while(0)
#endif

/*===========================================================================
 * Prefetch Hints
 *===========================================================================*/

#if defined(TL_COMPILER_MSVC)
    #include <intrin.h>
    #define TL_PREFETCH_READ(addr)  _mm_prefetch((const char*)(addr), _MM_HINT_T0)
    #define TL_PREFETCH_WRITE(addr) _mm_prefetch((const char*)(addr), _MM_HINT_T0)
#elif defined(TL_COMPILER_GCC) || defined(TL_COMPILER_CLANG)
    #define TL_PREFETCH_READ(addr)  __builtin_prefetch((addr), 0, 3)
    #define TL_PREFETCH_WRITE(addr) __builtin_prefetch((addr), 1, 3)
#else
    #define TL_PREFETCH_READ(addr)  ((void)(addr))
    #define TL_PREFETCH_WRITE(addr) ((void)(addr))
#endif

#endif /* TL_PLATFORM_H */
