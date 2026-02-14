#ifndef TL_FORMAL_TRACE_H
#define TL_FORMAL_TRACE_H

#include "tl_defs.h"

typedef struct tl_formal_trace_event {
    const char* ev;
    tl_seq_t seq;
    tl_ts_t t1;
    tl_ts_t t2;
    uint64_t src0;
    uint64_t src1;
    uint64_t wm0;
    uint64_t wm1;
    tl_seq_t snap_seq;
    uint64_t digest;
    int32_t status;
} tl_formal_trace_event_t;

#ifdef TL_FORMAL_TRACE
void tl_formal_trace_emit(const tl_formal_trace_event_t* ev);
#else
TL_INLINE void tl_formal_trace_emit(const tl_formal_trace_event_t* ev) {
    (void)ev;
}
#endif

#endif /* TL_FORMAL_TRACE_H */
