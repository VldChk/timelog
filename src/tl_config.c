#include "internal/tl_config.h"
#include <string.h>

tl_status_t tl_config_init_defaults(tl_config_t* cfg) {
    if (cfg == NULL) {
        return TL_EINVAL;
    }

    memset(cfg, 0, sizeof(*cfg));

    cfg->time_unit = TL_TIME_MS;
    cfg->target_page_bytes = TL_DEFAULT_PAGE_BYTES;
    cfg->memtable_max_bytes = TL_DEFAULT_MEMTABLE_BYTES;
    cfg->max_delta_segments = TL_DEFAULT_MAX_DELTA_SEGS;
    cfg->maintenance_mode = TL_MAINT_DISABLED;

    /* Initialize allocator to defaults (uses libc) */
    tl_allocator_init_default(&cfg->allocator);

    /* Logging disabled by default */
    cfg->log_fn = NULL;
    cfg->log_ctx = NULL;

    /* No drop callback by default */
    cfg->on_drop_handle = NULL;
    cfg->on_drop_ctx = NULL;

    return TL_OK;
}

tl_status_t tl_config_validate(const tl_config_t* cfg) {
    if (cfg == NULL) {
        return TL_EINVAL;
    }

    /* Validate time unit */
    if (cfg->time_unit > TL_TIME_NS) {
        return TL_EINVAL;
    }

    /* Validate page size (minimum 1 KiB, maximum 16 MiB) */
    if (cfg->target_page_bytes < 1024 || cfg->target_page_bytes > 16 * 1024 * 1024) {
        return TL_EINVAL;
    }

    /* Validate memtable size (minimum 16 KiB) */
    if (cfg->memtable_max_bytes < 16 * 1024) {
        return TL_EINVAL;
    }

    /* Validate delta segments (minimum 1) */
    if (cfg->max_delta_segments < 1) {
        return TL_EINVAL;
    }

    /* Validate maintenance mode */
    if (cfg->maintenance_mode > TL_MAINT_BACKGROUND) {
        return TL_EINVAL;
    }

    return TL_OK;
}
