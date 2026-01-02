#ifndef TL_LOG_H
#define TL_LOG_H

#include "tl_defs.h"
#include <stdarg.h>

/*===========================================================================
 * Log Levels
 *===========================================================================*/

typedef enum tl_log_level {
    TL_LOG_LEVEL_ERROR = 0,
    TL_LOG_LEVEL_WARN  = 1,
    TL_LOG_LEVEL_INFO  = 2,
    TL_LOG_LEVEL_DEBUG = 3,
    TL_LOG_LEVEL_TRACE = 4
} tl_log_level_t;

/*===========================================================================
 * Log Context
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
 */
void tl__log_init(tl_log_ctx_t* log, tl_log_fn fn, void* ctx);

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
    tl__log(log, TL_LOG_LEVEL_ERROR, __VA_ARGS__)

#define TL_LOG_WARN(...) \
    tl__log(log, TL_LOG_LEVEL_WARN, __VA_ARGS__)

#define TL_LOG_INFO(...) \
    tl__log(log, TL_LOG_LEVEL_INFO, __VA_ARGS__)

#ifdef TL_DEBUG
    #define TL_LOG_DEBUG(...) \
        tl__log(log, TL_LOG_LEVEL_DEBUG, __VA_ARGS__)
    #define TL_LOG_TRACE(...) \
        tl__log(log, TL_LOG_LEVEL_TRACE, __VA_ARGS__)
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
