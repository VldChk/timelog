#include "../internal/tl_manifest.h"
#include <string.h>

/*
 * Internal: destroy manifest resources.
 */
static void manifest_destroy(tl_manifest_t* m) {
    if (m == NULL) return;

    const tl_allocator_t* alloc = m->alloc;

    /* Release all main segments */
    for (uint32_t i = 0; i < m->n_main; i++) {
        if (m->main[i] != NULL) {
            tl_segment_release(m->main[i]);
        }
    }
    if (m->main != NULL) {
        tl__free(alloc, m->main);
    }

    /* Release all delta segments */
    for (uint32_t i = 0; i < m->n_delta; i++) {
        if (m->delta[i] != NULL) {
            tl_segment_release(m->delta[i]);
        }
    }
    if (m->delta != NULL) {
        tl__free(alloc, m->delta);
    }

    /* Free manifest itself */
    tl__free(alloc, m);
}

tl_status_t tl_manifest_create_empty(const tl_allocator_t* alloc,
                                      uint64_t version,
                                      tl_manifest_t** out) {
    if (out == NULL) return TL_EINVAL;
    *out = NULL;

    tl_manifest_t* m = tl__calloc(alloc, 1, sizeof(tl_manifest_t));
    if (m == NULL) return TL_ENOMEM;

    m->alloc = alloc;
    m->version = version;
    m->n_main = 0;
    m->main = NULL;
    m->n_delta = 0;
    m->delta = NULL;
    m->has_bounds = false;
    tl_atomic_u32_store(&m->refcnt, 1);

    *out = m;
    return TL_OK;
}

/*
 * Helper: check if segment is in removal list.
 */
static bool in_removal_list(tl_segment_t* seg, tl_segment_t** list, uint32_t n) {
    for (uint32_t i = 0; i < n; i++) {
        if (list[i] == seg) return true;
    }
    return false;
}

tl_status_t tl_manifest_build(const tl_allocator_t* alloc,
                               const tl_manifest_t* old,
                               tl_segment_t* add_delta,
                               tl_segment_t* add_main,
                               tl_segment_t** remove_delta,
                               uint32_t n_remove_delta,
                               tl_segment_t** remove_main,
                               uint32_t n_remove_main,
                               tl_manifest_t** out) {
    if (out == NULL) return TL_EINVAL;
    *out = NULL;

    /* Allocate new manifest */
    tl_manifest_t* m = tl__calloc(alloc, 1, sizeof(tl_manifest_t));
    if (m == NULL) return TL_ENOMEM;

    m->alloc = alloc;
    m->version = old ? old->version + 1 : 1;
    tl_atomic_u32_store(&m->refcnt, 1);

    /* Calculate new segment counts */
    uint32_t old_n_main = old ? old->n_main : 0;
    uint32_t old_n_delta = old ? old->n_delta : 0;

    uint32_t new_n_main = old_n_main - n_remove_main + (add_main ? 1 : 0);
    uint32_t new_n_delta = old_n_delta - n_remove_delta + (add_delta ? 1 : 0);

    /* Allocate main segment array */
    if (new_n_main > 0) {
        m->main = tl__malloc(alloc, new_n_main * sizeof(tl_segment_t*));
        if (m->main == NULL) {
            tl__free(alloc, m);
            return TL_ENOMEM;
        }
    }

    /* Allocate delta segment array */
    if (new_n_delta > 0) {
        m->delta = tl__malloc(alloc, new_n_delta * sizeof(tl_segment_t*));
        if (m->delta == NULL) {
            if (m->main) tl__free(alloc, m->main);
            tl__free(alloc, m);
            return TL_ENOMEM;
        }
    }

    /* Copy main segments (excluding removed ones) */
    uint32_t idx = 0;
    for (uint32_t i = 0; i < old_n_main; i++) {
        tl_segment_t* seg = old->main[i];
        if (!in_removal_list(seg, remove_main, n_remove_main)) {
            tl_segment_acquire(seg);
            m->main[idx++] = seg;
        }
    }

    /* Add new main segment */
    if (add_main) {
        tl_segment_acquire(add_main);
        m->main[idx++] = add_main;
    }
    m->n_main = idx;

    /* Copy delta segments (excluding removed ones) */
    idx = 0;
    for (uint32_t i = 0; i < old_n_delta; i++) {
        tl_segment_t* seg = old->delta[i];
        if (!in_removal_list(seg, remove_delta, n_remove_delta)) {
            tl_segment_acquire(seg);
            m->delta[idx++] = seg;
        }
    }

    /* Add new delta segment */
    if (add_delta) {
        tl_segment_acquire(add_delta);
        m->delta[idx++] = add_delta;
    }
    m->n_delta = idx;

    /* Compute bounds */
    tl_manifest_compute_bounds(m);

    *out = m;
    return TL_OK;
}

uint32_t tl_manifest_acquire(tl_manifest_t* m) {
    if (m == NULL) return 0;
    return tl_atomic_u32_fetch_add(&m->refcnt, 1) + 1;
}

uint32_t tl_manifest_release(tl_manifest_t* m) {
    if (m == NULL) return 0;

    uint32_t old = tl_atomic_u32_fetch_sub(&m->refcnt, 1);
    if (old == 1) {
        manifest_destroy(m);
        return 0;
    }
    return old - 1;
}

void tl_manifest_compute_bounds(tl_manifest_t* m) {
    if (m == NULL) return;

    if (m->n_main == 0 && m->n_delta == 0) {
        m->has_bounds = false;
        return;
    }

    tl_ts_t min_ts = TL_TS_MAX;
    tl_ts_t max_ts = TL_TS_MIN;

    for (uint32_t i = 0; i < m->n_main; i++) {
        if (m->main[i]->min_ts < min_ts) min_ts = m->main[i]->min_ts;
        if (m->main[i]->max_ts > max_ts) max_ts = m->main[i]->max_ts;
    }

    for (uint32_t i = 0; i < m->n_delta; i++) {
        if (m->delta[i]->min_ts < min_ts) min_ts = m->delta[i]->min_ts;
        if (m->delta[i]->max_ts > max_ts) max_ts = m->delta[i]->max_ts;
    }

    m->min_ts = min_ts;
    m->max_ts = max_ts;
    m->has_bounds = true;
}

tl_status_t tl_manifest_validate(const tl_manifest_t* m) {
    if (m == NULL) return TL_OK;

    /* Check all segment pointers are non-NULL */
    for (uint32_t i = 0; i < m->n_main; i++) {
        if (m->main[i] == NULL) return TL_EINTERNAL;
    }
    for (uint32_t i = 0; i < m->n_delta; i++) {
        if (m->delta[i] == NULL) return TL_EINTERNAL;
    }

    /* Validate each segment */
    for (uint32_t i = 0; i < m->n_main; i++) {
        tl_status_t st = tl_segment_validate(m->main[i]);
        if (st != TL_OK) return st;
    }
    for (uint32_t i = 0; i < m->n_delta; i++) {
        tl_status_t st = tl_segment_validate(m->delta[i]);
        if (st != TL_OK) return st;
    }

    /* Validate cached bounds if present */
    if (m->has_bounds && (m->n_main > 0 || m->n_delta > 0)) {
        tl_ts_t min_ts = TL_TS_MAX;
        tl_ts_t max_ts = TL_TS_MIN;

        for (uint32_t i = 0; i < m->n_main; i++) {
            if (m->main[i]->min_ts < min_ts) min_ts = m->main[i]->min_ts;
            if (m->main[i]->max_ts > max_ts) max_ts = m->main[i]->max_ts;
        }
        for (uint32_t i = 0; i < m->n_delta; i++) {
            if (m->delta[i]->min_ts < min_ts) min_ts = m->delta[i]->min_ts;
            if (m->delta[i]->max_ts > max_ts) max_ts = m->delta[i]->max_ts;
        }

        if (m->min_ts != min_ts || m->max_ts != max_ts) {
            return TL_EINTERNAL;
        }
    }

    return TL_OK;
}
