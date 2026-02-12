#include "tl_formal_trace.h"

#ifdef TL_FORMAL_TRACE

#include <stdio.h>
#include <inttypes.h>

void tl_formal_trace_emit(const tl_formal_trace_event_t* ev) {
    if (ev == NULL || ev->ev == NULL) {
        return;
    }

    fprintf(stderr,
            "TLTRACE ev=%s seq=%" PRIu64 " t1=%" PRId64 " t2=%" PRId64
            " src0=%" PRIu64 " src1=%" PRIu64
            " wm0=%" PRIu64 " wm1=%" PRIu64
            " snap=%" PRIu64 " digest=%" PRIu64 " st=%" PRId32 "\n",
            ev->ev,
            (uint64_t)ev->seq,
            (int64_t)ev->t1,
            (int64_t)ev->t2,
            ev->src0,
            ev->src1,
            ev->wm0,
            ev->wm1,
            (uint64_t)ev->snap_seq,
            ev->digest,
            ev->status);
}

#endif
