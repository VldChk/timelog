#ifndef TL_LOG_H
#define TL_LOG_H

#include "tl_defs.h"
#include <stdarg.h>

/*===========================================================================
 * Log Context
 *
 * Uses tl_log_level_t from public API (timelog/timelog.h, included via tl_defs.h).
 * Internal code uses TL_LOG_* values directly.
 *===========================================================================*/

typedef struct tl_log_ctx {
    tl_log_fn       fn;
    void*           ctx;
    tl_log_level_t  max_level;
} tl_log_ctx_t;

/*===========================================================================
 * Initialization
 *===========================================================================*/

/**
 * Initialize log context from user configuration.
 * If fn is NULL, logging is disabled.
 * @param level Max log level to accept (use TL_LOG_NONE to disable all)
 */
void tl__log_init(tl_log_ctx_t* log, tl_log_fn fn, void* ctx, tl_log_level_t level);

/*===========================================================================
 * Logging Functions
 *===========================================================================*/

/**
 * Log a message at the specified level.
 * Thread-safe if the user's log function is thread-safe.
 */
void tl__log(tl_log_ctx_t* log, tl_log_level_t level,
             const char* fmt, ...);

void tl__log_v(tl_log_ctx_t* log, tl_log_level_t level,
               const char* fmt, va_list args);

/*===========================================================================
 * Convenience Macros
 *
 * Note: These macros use __VA_ARGS__ without the ## GCC extension for
 * MSVC portability. The format string is included in __VA_ARGS__.
 *===========================================================================*/

/* These require a `tl_log_ctx_t* log` in scope */

#define TL_LOG_ERROR(...) \
    tl__log(log, TL_LOG_ERROR, __VA_ARGS__)

#define TL_LOG_WARN(...) \
    tl__log(log, TL_LOG_WARN, __VA_ARGS__)

#define TL_LOG_INFO(...) \
    tl__log(log, TL_LOG_INFO, __VA_ARGS__)

#ifdef TL_DEBUG
    #define TL_LOG_DEBUG(...) \
        tl__log(log, TL_LOG_DEBUG, __VA_ARGS__)
    #define TL_LOG_TRACE(...) \
        tl__log(log, TL_LOG_TRACE, __VA_ARGS__)
#else
    #define TL_LOG_DEBUG(...) ((void)0)
    #define TL_LOG_TRACE(...) ((void)0)
#endif

/*===========================================================================
 * Global Log Macros (for use before instance is created)
 *===========================================================================*/

/* These use a static null log context - effectively disabled */
#define TL_LOG_STATIC_ERROR(...) ((void)0)
#define TL_LOG_STATIC_WARN(...)  ((void)0)

#endif /* TL_LOG_H */
