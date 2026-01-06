#include "tl_log.h"
#include <stdio.h>
#include <string.h>

/*===========================================================================
 * Configuration
 *===========================================================================*/

#define TL_LOG_MAX_MESSAGE_LEN 1024

/*===========================================================================
 * Initialization
 *===========================================================================*/

void tl__log_init(tl_log_ctx_t* log, tl_log_fn fn, void* ctx) {
    TL_ASSERT(log != NULL);

    log->fn = fn;
    log->ctx = ctx;
    log->max_level = TL_LOG_LEVEL_TRACE; /* Accept all levels by default */
}

/*===========================================================================
 * Logging Implementation
 *===========================================================================*/

static const char* level_names[] = {
    "ERROR",
    "WARN",
    "INFO",
    "DEBUG",
    "TRACE"
};

void tl__log_v(tl_log_ctx_t* log, tl_log_level_t level,
               const char* fmt, va_list args) {
    if (log == NULL || log->fn == NULL) {
        return;
    }

    /* Validate level bounds before array access to prevent UB */
    if ((int)level < 0 || (int)level > (int)TL_LOG_LEVEL_TRACE) {
        return;
    }

    if (level > log->max_level) {
        return;
    }

    char buffer[TL_LOG_MAX_MESSAGE_LEN];
    int prefix_len;
    int msg_len;

    /* Format: "[LEVEL] message" */
    prefix_len = snprintf(buffer, sizeof(buffer), "[%s] ",
                          level_names[level]);

    if (prefix_len < 0 || (size_t)prefix_len >= sizeof(buffer)) {
        return;
    }

    msg_len = vsnprintf(buffer + prefix_len,
                        sizeof(buffer) - (size_t)prefix_len,
                        fmt, args);

    if (msg_len < 0) {
        /* Format error (encoding issue, etc.) - don't silently drop.
         * Log a placeholder so the user knows a log was attempted.
         * This helps catch format string bugs during development. */
        snprintf(buffer + prefix_len,
                 sizeof(buffer) - (size_t)prefix_len,
                 "<log format error>");
    }

    /* Call user's log function */
    log->fn(log->ctx, (int)level, buffer);
}

void tl__log(tl_log_ctx_t* log, tl_log_level_t level,
             const char* fmt, ...) {
    va_list args;
    va_start(args, fmt);
    tl__log_v(log, level, fmt, args);
    va_end(args);
}
