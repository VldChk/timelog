#include "internal/tl_log.h"
#include <stdio.h>
#include <stdarg.h>

void tl_logger_init_noop(tl_logger_t* logger) {
    if (logger == NULL) return;
    logger->fn = NULL;
    logger->ctx = NULL;
    logger->min_level = TL_LOG_OFF;
}

void tl_logger_init(tl_logger_t* logger, tl_log_fn_internal fn, void* ctx,
                    tl_log_level_t min_level) {
    if (logger == NULL) return;
    logger->fn = fn;
    logger->ctx = ctx;
    logger->min_level = min_level;
}

#if defined(TL_ENABLE_LOGGING) || !defined(NDEBUG)

/* Small buffer for formatting; avoids allocation in log path */
#define TL_LOG_BUF_SIZE 512

void tl__log(const tl_logger_t* logger, tl_log_level_t level,
             const char* file, int line, const char* fmt, ...) {
    if (logger == NULL || logger->fn == NULL) return;
    if (level < logger->min_level) return;

    char buf[TL_LOG_BUF_SIZE];
    va_list args;
    va_start(args, fmt);
    vsnprintf(buf, sizeof(buf), fmt, args);
    va_end(args);

    buf[TL_LOG_BUF_SIZE - 1] = '\0';  /* Ensure null termination */
    logger->fn(logger->ctx, level, file, line, buf);
}

#endif /* TL_ENABLE_LOGGING || !NDEBUG */
