#ifndef TL_IMMUTABLE_COUNT_H
#define TL_IMMUTABLE_COUNT_H

#include "../internal/tl_defs.h"
#include "../internal/tl_intervals.h"
#include "../delta/tl_memrun.h"
#include "../storage/tl_segment.h"

uint64_t tl_count_records_in_memrun_range(const tl_memrun_t* mr,
                                          tl_ts_t a,
                                          tl_ts_t b,
                                          bool b_unbounded);

uint64_t tl_count_visible_records_in_segment_range(const tl_segment_t* seg,
                                                   tl_ts_t a,
                                                   tl_ts_t b,
                                                   bool b_unbounded,
                                                   const tl_interval_t* tombs,
                                                   size_t tomb_count);

uint64_t tl_count_visible_records_in_memrun_range(const tl_memrun_t* mr,
                                                  tl_ts_t a,
                                                  tl_ts_t b,
                                                  bool b_unbounded,
                                                  const tl_interval_t* tombs,
                                                  size_t tomb_count);

#endif
