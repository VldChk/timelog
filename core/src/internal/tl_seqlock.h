#ifndef TL_SEQLOCK_H
#define TL_SEQLOCK_H

#include "tl_atomic.h"

/*===========================================================================
 * Seqlock for Snapshot Consistency
 *
 * Protocol:
 *
 * Writer (publication):
 *   1. Lock writer_mu
 *   2. view_seq++ (odd = publish in progress)
 *   3. Swap manifest pointer + update memtable state
 *   4. view_seq++ (even = publish complete)
 *   5. Unlock writer_mu
 *
 * Reader (snapshot acquisition):
 *   1. Lock writer_mu (required because we also capture memview)
 *   2. seq1 = load view_seq (must be even)
 *   3. Acquire manifest ref + capture memview
 *   4. seq2 = load view_seq
 *   5. Unlock writer_mu
 *   6. If seq1 != seq2 OR seq1 is odd: retry
 *
 * Note: Unlike a pure seqlock, we hold writer_mu during snapshot to ensure
 * the memview capture is consistent with manifest. The seqlock counter
 * provides an additional consistency check and enables future lock-free
 * optimizations.
 *===========================================================================*/

/*
 * Cache line size for padding calculations.
 * Use the platform definition if available, otherwise default to 64 bytes.
 * 64 bytes is correct for x86-64, ARM64, and most modern architectures.
 * Using padding instead of alignment attributes avoids overalignment UB
 * since malloc only guarantees 16-byte alignment (or 8 on some platforms).
 */
#ifndef TL_CACHE_LINE_SIZE
#define TL_CACHE_LINE_SIZE 64
#endif

/*
 * Verify that cache line size is large enough for padding calculation.
 * If TL_CACHE_LINE_SIZE is overridden to a small value, the padding
 * calculation would underflow. Minimum is sizeof(tl_atomic_u64) + 1.
 */
#if TL_CACHE_LINE_SIZE <= 8
#error "TL_CACHE_LINE_SIZE must be greater than sizeof(tl_atomic_u64) (8 bytes)"
#endif

typedef struct tl_seqlock {
    tl_atomic_u64 seq;
    /*
     * Padding to reduce false sharing with adjacent data.
     * Note: Without alignment, we cannot guarantee the seqlock starts at
     * a cache line boundary. The padding ensures the atomic counter
     * doesn't span cache lines and reduces (but doesn't eliminate) the
     * chance of sharing a line with unrelated data.
     */
    char _pad[TL_CACHE_LINE_SIZE - sizeof(tl_atomic_u64)];
} tl_seqlock_t;

/**
 * Initialize seqlock to even value (0 = idle).
 */
TL_INLINE void tl_seqlock_init(tl_seqlock_t* sl) {
    TL_ASSERT(sl != NULL);
    tl_atomic_init_u64(&sl->seq, 0);
}

/**
 * Begin write (increment to odd).
 * Must be called under writer_mu.
 *
 * Uses ACQ_REL ordering:
 * - ACQUIRE: Ensures we see any prior writes before starting our write
 * - RELEASE: Ensures the odd counter is visible before we start modifying data
 * This creates a full barrier that prevents reordering in both directions.
 */
TL_INLINE void tl_seqlock_write_begin(tl_seqlock_t* sl) {
    TL_ASSERT(sl != NULL);
    tl_atomic_fetch_add_u64(&sl->seq, 1, TL_MO_ACQ_REL);
#ifdef TL_DEBUG
    /* Verify we're now odd - only check in debug to avoid extra atomic load */
    TL_ASSERT((tl_atomic_load_relaxed_u64(&sl->seq) & 1) == 1);
#endif
}

/**
 * End write (increment to even).
 * Must be called under writer_mu.
 */
TL_INLINE void tl_seqlock_write_end(tl_seqlock_t* sl) {
    TL_ASSERT(sl != NULL);
#ifdef TL_DEBUG
    /* Verify we're currently odd - only check in debug to avoid extra atomic load */
    TL_ASSERT((tl_atomic_load_relaxed_u64(&sl->seq) & 1) == 1);
#endif
    tl_atomic_fetch_add_u64(&sl->seq, 1, TL_MO_RELEASE);
}

/**
 * Read seqlock value (for consistency check).
 * Returns the current sequence number.
 */
TL_INLINE uint64_t tl_seqlock_read(const tl_seqlock_t* sl) {
    TL_ASSERT(sl != NULL);
    return tl_atomic_load_acquire_u64(&sl->seq);
}

/**
 * Check if sequence is even (no write in progress).
 */
TL_INLINE bool tl_seqlock_is_even(uint64_t seq) {
    return (seq & 1) == 0;
}

/**
 * Validate read consistency.
 * @param seq1 Value read before operation
 * @param seq2 Value read after operation
 * @return true if consistent (seq1 == seq2 and both even)
 */
TL_INLINE bool tl_seqlock_validate(uint64_t seq1, uint64_t seq2) {
    return (seq1 == seq2) && tl_seqlock_is_even(seq1);
}

/**
 * Get current sequence number (for debugging/metrics).
 */
TL_INLINE uint64_t tl_seqlock_current(const tl_seqlock_t* sl) {
    TL_ASSERT(sl != NULL);
    return tl_atomic_load_relaxed_u64(&sl->seq);
}

#endif /* TL_SEQLOCK_H */
