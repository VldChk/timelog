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
    #define TL_INLINE        static __forceinline
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
 * WARNING: TL_ASSERT maps to TL_ASSUME in release builds, which tells the
 * compiler the condition is always true. This is an optimization hint.
 *
 * NEVER use TL_ASSERT for:
 * - User input validation (use explicit checks + return TL_EINVAL)
 * - API contract enforcement on external data
 * - Anything that could be false due to caller error
 *
 * ONLY use TL_ASSERT for:
 * - Internal invariants provably true by construction
 * - Programmer errors that indicate bugs in timelog itself
 *===========================================================================*/

#ifdef TL_DEBUG
    #include <assert.h>
    #define TL_ASSERT(cond) assert(cond)
    #define TL_ASSERT_MSG(cond, msg) assert((cond) && (msg))
#else
    #define TL_ASSERT(cond) TL_ASSUME(cond)
    #define TL_ASSERT_MSG(cond, msg) TL_ASSUME(cond)
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
