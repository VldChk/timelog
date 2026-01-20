#ifndef TL_DEFS_H
#define TL_DEFS_H

#include "timelog/timelog.h"
#include "tl_platform.h"

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <string.h>

/*===========================================================================
 * Timestamp Bounds
 *===========================================================================*/

#define TL_TS_MIN  INT64_MIN
#define TL_TS_MAX  INT64_MAX

/*===========================================================================
 * Size Constants
 *===========================================================================*/

/* Default configuration values (use size_t to avoid implicit widening) */
#define TL_DEFAULT_TARGET_PAGE_BYTES      ((size_t)64 * 1024)   /* 64 KiB */
#define TL_DEFAULT_MEMTABLE_MAX_BYTES     ((size_t)1024 * 1024) /* 1 MiB */
#define TL_DEFAULT_SEALED_MAX_RUNS        4
#define TL_DEFAULT_SEALED_WAIT_MS         100
#define TL_DEFAULT_MAINTENANCE_WAKEUP_MS  100   /* Periodic wake interval */
#define TL_DEFAULT_MAX_DELTA_SEGMENTS     8

/* Minimum page rows to prevent degenerate pages */
#define TL_MIN_PAGE_ROWS                  16

/* Record size for byte accounting (use actual struct size to handle padding) */
#define TL_RECORD_SIZE                    (sizeof(tl_record_t))

/*===========================================================================
 * Type Size/Layout Validation
 *
 * Static asserts to catch platform issues at compile time.
 * These assumptions are critical for:
 * - Memory accounting (TL_RECORD_SIZE)
 * - Page layout calculations
 * - Serialization compatibility (if added later)
 *===========================================================================*/

_Static_assert(sizeof(tl_ts_t) == 8,
    "tl_ts_t must be 8 bytes (int64_t)");
_Static_assert(sizeof(tl_handle_t) == 8,
    "tl_handle_t must be 8 bytes (uint64_t)");
_Static_assert(sizeof(tl_record_t) == 16,
    "tl_record_t must be 16 bytes (ts + handle, no padding)");
_Static_assert(_Alignof(tl_record_t) == 8,
    "tl_record_t must be 8-byte aligned for efficient access");

/*===========================================================================
 * Window Defaults (in time units)
 *===========================================================================*/

/* 1 hour in each time unit */
#define TL_WINDOW_1H_S   (3600LL)
#define TL_WINDOW_1H_MS  (3600LL * 1000)
#define TL_WINDOW_1H_US  (3600LL * 1000 * 1000)
#define TL_WINDOW_1H_NS  (3600LL * 1000 * 1000 * 1000)

/*===========================================================================
 * Forward Declarations (Internal Types)
 *===========================================================================*/

/* Storage layer */
typedef struct tl_page          tl_page_t;
typedef struct tl_page_meta     tl_page_meta_t;
typedef struct tl_page_catalog  tl_page_catalog_t;
typedef struct tl_segment       tl_segment_t;
typedef struct tl_manifest      tl_manifest_t;
typedef struct tl_tombstones    tl_tombstones_t;

/* Delta layer */
typedef struct tl_memtable      tl_memtable_t;
typedef struct tl_memrun        tl_memrun_t;
typedef struct tl_memview       tl_memview_t;
typedef struct tl_flush_ctx     tl_flush_ctx_t;
typedef struct tl_merge_iter    tl_merge_iter_t;

/* Tombstones */
typedef struct tl_interval      tl_interval_t;
typedef struct tl_intervals     tl_intervals_t;

/* Maintenance */
typedef struct tl_maint_state   tl_maint_state_t;

/*===========================================================================
 * Internal Helper Macros
 *===========================================================================*/

/* Safe minimum/maximum */
#define TL_MIN(a, b) (((a) < (b)) ? (a) : (b))
#define TL_MAX(a, b) (((a) > (b)) ? (a) : (b))

/* Array element count */
#define TL_ARRAY_SIZE(arr) (sizeof(arr) / sizeof((arr)[0]))

/* Pointer alignment check */
#define TL_IS_ALIGNED(ptr, align) (((uintptr_t)(ptr) & ((align) - 1)) == 0)

/* Round up to power of 2 alignment */
#define TL_ALIGN_UP(x, align) (((x) + ((align) - 1)) & ~((align) - 1))

/*===========================================================================
 * Internal Allocator Access
 *===========================================================================*/

/* These are defined in tl_alloc.h but forward-declared here for convenience */
struct tl_alloc_ctx;
typedef struct tl_alloc_ctx tl_alloc_ctx_t;

#endif /* TL_DEFS_H */
