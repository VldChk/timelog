#ifndef TL_CONFIG_H
#define TL_CONFIG_H

/*
 * Internal configuration header.
 * Re-exports config types from public header and adds validation/defaults.
 */
#include "tl_status.h"
#include "tl_alloc.h"
#include "tl_log.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Validate configuration values.
 *
 * @param cfg Config to validate
 * @return TL_OK if valid, TL_EINVAL if invalid
 */
tl_status_t tl_config_validate(const tl_config_t* cfg);

/*
 * Default values (exposed for documentation/testing)
 */
#define TL_DEFAULT_PAGE_BYTES      (64 * 1024)      /* 64 KiB */
#define TL_DEFAULT_MEMTABLE_BYTES  (1024 * 1024)    /* 1 MiB */
#define TL_DEFAULT_MAX_DELTA_SEGS  4

#ifdef __cplusplus
}
#endif

#endif /* TL_CONFIG_H */
