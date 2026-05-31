#ifndef TL_SEQLOCK_H
#define TL_SEQLOCK_H

#include "tl_atomic.h"

/*===========================================================================
 * Seqlock for Snapshot Consistency
 *
 * Pattern: a 64-bit counter that is incremented twice around every
 * publication — once before the visible mutation (making the counter odd
 * to advertise "writer in progress"), once after (returning it to even).
 * Readers sample the counter before and after capturing state; equal even
 * values guarantee the capture observed a single coherent moment in time.
 *
 * Protocol (writer): lock writer_mu, increment to odd, mutate, increment
 * to even, unlock. Protocol (reader): lock writer_mu, read seq1, capture
 * manifest + memview, read seq2, unlock; retry if seq1 != seq2 or odd.
 *
 * The reader path still holds writer_mu because memview capture touches
 * memtable state that the seqlock alone cannot protect. The seqlock
 * counter doubles as a consistency check and as a hook for future
 * lock-free optimisations on the read side.
 *===========================================================================*/

/*
 * Cache-line size used for trailing padding. 64 bytes covers x86-64,
 * ARM64, and most modern hardware. Padding is preferable to an alignment
 * attribute here because malloc only guarantees 16-byte alignment, so
 * over-aligning would invoke undefined behaviour on heap-allocated owners.
 */
#ifndef TL_CACHE_LINE_SIZE
#define TL_CACHE_LINE_SIZE 64
#endif

/* The padding size below must not underflow if a downstream build forces
 * a smaller cache line size — bail out at compile time if so. */
#if TL_CACHE_LINE_SIZE <= 8
#error "TL_CACHE_LINE_SIZE must be greater than sizeof(tl_atomic_u64) (8 bytes)"
#endif

typedef struct tl_seqlock {
    tl_atomic_u64 seq;
    /*
     * Trailing padding to mitigate (not eliminate) false sharing. Without
     * an alignment guarantee on the embedding struct we can't promise the
     * counter starts at a cache-line boundary, but padding to a line size
     * at least prevents the counter from spilling into a neighbour's line.
     */
    char _pad[TL_CACHE_LINE_SIZE - sizeof(tl_atomic_u64)];
} tl_seqlock_t;

/** Initialise to the even idle value 0. */
TL_INLINE void tl_seqlock_init(tl_seqlock_t* sl) {
    TL_ASSERT(sl != NULL);
    tl_atomic_init_u64(&sl->seq, 0);
}

/**
 * Mark publication start by incrementing the counter to odd. Must be
 * called with writer_mu held. ACQ_REL ordering is mandatory: the acquire
 * half ensures we observe everything published before us, the release
 * half ensures readers see the odd counter before any mutation that
 * follows it.
 */
TL_INLINE void tl_seqlock_write_begin(tl_seqlock_t* sl) {
    TL_ASSERT(sl != NULL);
    tl_atomic_fetch_add_u64(&sl->seq, 1, TL_MO_ACQ_REL);
#ifdef TL_DEBUG
    TL_ASSERT((tl_atomic_load_relaxed_u64(&sl->seq) & 1) == 1);
#endif
}

/**
 * Mark publication end by incrementing the counter back to even. Must be
 * called with writer_mu held. Release ordering ensures readers that
 * observe the new even value also observe all preceding mutations.
 */
TL_INLINE void tl_seqlock_write_end(tl_seqlock_t* sl) {
    TL_ASSERT(sl != NULL);
#ifdef TL_DEBUG
    TL_ASSERT((tl_atomic_load_relaxed_u64(&sl->seq) & 1) == 1);
#endif
    tl_atomic_fetch_add_u64(&sl->seq, 1, TL_MO_RELEASE);
}

/** Snapshot the current sequence number with acquire ordering. */
TL_INLINE uint64_t tl_seqlock_read(const tl_seqlock_t* sl) {
    TL_ASSERT(sl != NULL);
    return tl_atomic_load_acquire_u64(&sl->seq);
}

/** Even counter == no publication is in progress. */
TL_INLINE bool tl_seqlock_is_even(uint64_t seq) {
    return (seq & 1) == 0;
}

/**
 * Two-sample consistency check.
 * @param seq1 Counter sampled before the read.
 * @param seq2 Counter sampled after the read.
 * @return true when both samples are equal and even (no publication
 *         crossed the read).
 */
TL_INLINE bool tl_seqlock_validate(uint64_t seq1, uint64_t seq2) {
    return (seq1 == seq2) && tl_seqlock_is_even(seq1);
}

/** Relaxed read for diagnostics and metrics; do not use for consistency. */
TL_INLINE uint64_t tl_seqlock_current(const tl_seqlock_t* sl) {
    TL_ASSERT(sl != NULL);
    return tl_atomic_load_relaxed_u64(&sl->seq);
}

#endif /* TL_SEQLOCK_H */
