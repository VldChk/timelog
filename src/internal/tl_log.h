#ifndef TL_LOG_H
#define TL_LOG_H

/*
 * Internal logging header.
 * Provides extended logging infrastructure beyond the public tl_log_fn.
 */
#include "../../include/timelog/timelog.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Log levels matching common conventions.
 */
typedef enum tl_log_level {
    TL_LOG_TRACE = 0,
    TL_LOG_DEBUG = 1,
    TL_LOG_INFO  = 2,
    TL_LOG_WARN  = 3,
    TL_LOG_ERROR = 4,
    TL_LOG_FATAL = 5,
    TL_LOG_OFF   = 6    /* Disable all logging */
} tl_log_level_t;

/**
 * Internal log callback signature (extended with file/line info).
 * Different from public tl_log_fn which is simpler.
 */
typedef void (*tl_log_fn_internal)(void* ctx, tl_log_level_t level,
                                   const char* file, int line, const char* msg);

/**
 * Logger context stored in timelog instance.
 */
typedef struct tl_logger {
    tl_log_fn_internal fn;
    void*              ctx;
    tl_log_level_t     min_level;
} tl_logger_t;

/**
 * Initialize logger to no-op (disabled).
 */
void tl_logger_init_noop(tl_logger_t* logger);

/**
 * Initialize logger with callback.
 */
void tl_logger_init(tl_logger_t* logger, tl_log_fn_internal fn, void* ctx,
                    tl_log_level_t min_level);

/**
 * Internal logging macros - these become no-ops in release builds
 * unless TL_ENABLE_LOGGING is defined.
 */
#if defined(TL_ENABLE_LOGGING) || !defined(NDEBUG)
void tl__log(const tl_logger_t* logger, tl_log_level_t level,
             const char* file, int line, const char* fmt, ...);

#define TL_LOG(logger, level, ...) \
    tl__log((logger), (level), __FILE__, __LINE__, __VA_ARGS__)
#else
#define TL_LOG(logger, level, ...) ((void)0)
#endif

#define TL_LOG_TRACE(logger, ...) TL_LOG(logger, TL_LOG_TRACE, __VA_ARGS__)
#define TL_LOG_DEBUG(logger, ...) TL_LOG(logger, TL_LOG_DEBUG, __VA_ARGS__)
#define TL_LOG_INFO(logger, ...)  TL_LOG(logger, TL_LOG_INFO, __VA_ARGS__)
#define TL_LOG_WARN(logger, ...)  TL_LOG(logger, TL_LOG_WARN, __VA_ARGS__)
#define TL_LOG_ERROR(logger, ...) TL_LOG(logger, TL_LOG_ERROR, __VA_ARGS__)

#ifdef __cplusplus
}
#endif

#endif /* TL_LOG_H */
