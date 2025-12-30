#include "../internal/tl_plan.h"
#include <string.h>

#define TL_PLAN_INITIAL_ITERS 8

/*
 * Add a component iterator to the plan.
 */
static tl_status_t plan_add_iter(tl_qplan_t* plan,
                                  const tl_iter_vtable_t* vtable,
                                  void* impl,
                                  uint32_t component_id) {
    /* Grow if needed */
    if (plan->n_iters >= plan->iters_cap) {
        uint32_t new_cap = plan->iters_cap * 2;
        if (new_cap == 0) new_cap = TL_PLAN_INITIAL_ITERS;

        tl_component_iter_t* new_iters = tl__realloc(plan->alloc, plan->iters,
                                                      new_cap * sizeof(tl_component_iter_t));
        if (new_iters == NULL) return TL_ENOMEM;

        plan->iters = new_iters;
        plan->iters_cap = new_cap;
    }

    plan->iters[plan->n_iters].vtable = vtable;
    plan->iters[plan->n_iters].impl = impl;
    plan->iters[plan->n_iters].component_id = component_id;
    plan->n_iters++;

    return TL_OK;
}

/*
 * Vtable adapters for segment iterator.
 */
static const tl_record_t* seg_iter_peek_adapter(void* self) {
    return tl_segment_iter_peek((tl_segment_iter_t*)self);
}

static tl_status_t seg_iter_advance_adapter(void* self) {
    return tl_segment_iter_advance((tl_segment_iter_t*)self);
}

static tl_status_t seg_iter_seek_adapter(void* self, tl_ts_t ts) {
    return tl_segment_iter_seek((tl_segment_iter_t*)self, ts);
}

static tl_iter_state_t seg_iter_state_adapter(void* self) {
    return tl_segment_iter_state((tl_segment_iter_t*)self);
}

static void seg_iter_destroy_adapter(void* self) {
    tl_segment_iter_destroy((tl_segment_iter_t*)self);
}

static const tl_iter_vtable_t segment_iter_vtable = {
    .peek = seg_iter_peek_adapter,
    .advance = seg_iter_advance_adapter,
    .seek = seg_iter_seek_adapter,
    .state = seg_iter_state_adapter,
    .destroy = seg_iter_destroy_adapter
};

/*
 * Vtable adapters for two-way iterator.
 */
static const tl_record_t* twoway_iter_peek_adapter(void* self) {
    return tl_twoway_iter_peek((tl_twoway_iter_t*)self);
}

static tl_status_t twoway_iter_advance_adapter(void* self) {
    return tl_twoway_iter_advance((tl_twoway_iter_t*)self);
}

static tl_status_t twoway_iter_seek_adapter(void* self, tl_ts_t ts) {
    return tl_twoway_iter_seek((tl_twoway_iter_t*)self, ts);
}

static tl_iter_state_t twoway_iter_state_adapter(void* self) {
    return tl_twoway_iter_state((tl_twoway_iter_t*)self);
}

static void twoway_iter_destroy_adapter(void* self) {
    tl_twoway_iter_destroy((tl_twoway_iter_t*)self);
}

static const tl_iter_vtable_t twoway_iter_vtable = {
    .peek = twoway_iter_peek_adapter,
    .advance = twoway_iter_advance_adapter,
    .seek = twoway_iter_seek_adapter,
    .state = twoway_iter_state_adapter,
    .destroy = twoway_iter_destroy_adapter
};

/*
 * Collect tombstones from all sources into intervals set.
 * Clips intervals to [t1, t2).
 */
static tl_status_t collect_tombstones(const tl_allocator_t* alloc,
                                       const tl_snapshot_t* snap,
                                       tl_ts_t t1,
                                       tl_ts_t t2,
                                       tl_intervals_t* out) {
    tl_intervals_init(out, alloc);
    tl_status_t st;

    /* Collect from manifest segments */
    if (snap->manifest != NULL) {
        /* Delta segments */
        for (uint32_t i = 0; i < snap->manifest->n_delta; i++) {
            const tl_segment_t* seg = snap->manifest->delta[i];
            if (seg->tombstones != NULL && !tl_tombstones_empty(seg->tombstones)) {
                for (uint32_t j = 0; j < seg->tombstones->n; j++) {
                    const tl_interval_t* iv = &seg->tombstones->v[j];
                    /* Clip to [t1, t2) */
                    tl_ts_t start = (iv->start > t1) ? iv->start : t1;
                    tl_ts_t end = (iv->end < t2) ? iv->end : t2;
                    if (start < end) {
                        st = tl_intervals_insert(out, start, end);
                        if (st != TL_OK) return st;
                    }
                }
            }
        }

        /* Main segments */
        for (uint32_t i = 0; i < snap->manifest->n_main; i++) {
            const tl_segment_t* seg = snap->manifest->main[i];
            if (seg->tombstones != NULL && !tl_tombstones_empty(seg->tombstones)) {
                for (uint32_t j = 0; j < seg->tombstones->n; j++) {
                    const tl_interval_t* iv = &seg->tombstones->v[j];
                    tl_ts_t start = (iv->start > t1) ? iv->start : t1;
                    tl_ts_t end = (iv->end < t2) ? iv->end : t2;
                    if (start < end) {
                        st = tl_intervals_insert(out, start, end);
                        if (st != TL_OK) return st;
                    }
                }
            }
        }
    }

    /* Collect from memview */
    if (snap->memview != NULL) {
        /* Active tombstones */
        for (size_t i = 0; i < snap->memview->active_tombs_len; i++) {
            const tl_interval_t* iv = &snap->memview->active_tombs[i];
            tl_ts_t start = (iv->start > t1) ? iv->start : t1;
            tl_ts_t end = (iv->end < t2) ? iv->end : t2;
            if (start < end) {
                st = tl_intervals_insert(out, start, end);
                if (st != TL_OK) return st;
            }
        }

        /* Sealed memrun tombstones */
        for (size_t i = 0; i < snap->memview->sealed_len; i++) {
            const tl_memrun_t* mr = snap->memview->sealed[i];
            for (size_t j = 0; j < mr->tombs_len; j++) {
                const tl_interval_t* iv = &mr->tombs[j];
                tl_ts_t start = (iv->start > t1) ? iv->start : t1;
                tl_ts_t end = (iv->end < t2) ? iv->end : t2;
                if (start < end) {
                    st = tl_intervals_insert(out, start, end);
                    if (st != TL_OK) return st;
                }
            }
        }
    }

    return TL_OK;
}

/*
 * Check if memrun overlaps with query range.
 */
static bool memrun_overlaps(const tl_memrun_t* mr, tl_ts_t t1, tl_ts_t t2) {
    if (mr == NULL) return false;
    if (mr->run_len == 0 && mr->ooo_len == 0) return false;
    return mr->max_ts >= t1 && mr->min_ts < t2;
}

tl_status_t tl_qplan_build(const tl_allocator_t* alloc,
                            const tl_snapshot_t* snap,
                            tl_ts_t t1,
                            tl_ts_t t2,
                            tl_qplan_t** out) {
    if (out == NULL) return TL_EINVAL;
    *out = NULL;

    if (t2 < t1) return TL_EINVAL;

    /* Allocate plan */
    tl_qplan_t* plan = tl__calloc(alloc, 1, sizeof(tl_qplan_t));
    if (plan == NULL) return TL_ENOMEM;

    plan->alloc = alloc;
    plan->t1 = t1;
    plan->t2 = t2;

    /* Empty range: return empty plan */
    if (t1 == t2 || snap == NULL) {
        *out = plan;
        return TL_OK;
    }

    tl_status_t st;
    uint32_t component_id = 0;

    /* Add segment iterators from manifest */
    if (snap->manifest != NULL) {
        /* Delta segments (scan all, may overlap) */
        for (uint32_t i = 0; i < snap->manifest->n_delta; i++) {
            const tl_segment_t* seg = snap->manifest->delta[i];
            if (seg->record_count == 0) continue;  /* Tombstone-only segment */
            if (!tl_segment_overlaps(seg, t1, t2)) continue;

            tl_segment_iter_t* it = NULL;
            st = tl_segment_iter_create(alloc, seg, t1, t2, &it);
            if (st != TL_OK) {
                tl_qplan_destroy(plan);
                return st;
            }

            /* Only add if iterator has data */
            if (tl_segment_iter_state(it) == TL_ITER_READY) {
                st = plan_add_iter(plan, &segment_iter_vtable, it, component_id++);
                if (st != TL_OK) {
                    tl_segment_iter_destroy(it);
                    tl_qplan_destroy(plan);
                    return st;
                }
            } else {
                tl_segment_iter_destroy(it);
            }
        }

        /* Main segments (sorted by min_ts) */
        for (uint32_t i = 0; i < snap->manifest->n_main; i++) {
            const tl_segment_t* seg = snap->manifest->main[i];
            if (seg->record_count == 0) continue;
            if (!tl_segment_overlaps(seg, t1, t2)) continue;

            tl_segment_iter_t* it = NULL;
            st = tl_segment_iter_create(alloc, seg, t1, t2, &it);
            if (st != TL_OK) {
                tl_qplan_destroy(plan);
                return st;
            }

            if (tl_segment_iter_state(it) == TL_ITER_READY) {
                st = plan_add_iter(plan, &segment_iter_vtable, it, component_id++);
                if (st != TL_OK) {
                    tl_segment_iter_destroy(it);
                    tl_qplan_destroy(plan);
                    return st;
                }
            } else {
                tl_segment_iter_destroy(it);
            }
        }
    }

    /* Add memview iterators */
    if (snap->memview != NULL) {
        /* Active buffers (2-way merge of run + ooo) */
        if (snap->memview->active_run_len > 0 || snap->memview->active_ooo_len > 0) {
            /* Check if active data overlaps with query range */
            bool has_data = false;
            tl_ts_t active_min = TL_TS_MAX;
            tl_ts_t active_max = TL_TS_MIN;

            if (snap->memview->active_run_len > 0) {
                has_data = true;
                if (snap->memview->active_run[0].ts < active_min)
                    active_min = snap->memview->active_run[0].ts;
                if (snap->memview->active_run[snap->memview->active_run_len - 1].ts > active_max)
                    active_max = snap->memview->active_run[snap->memview->active_run_len - 1].ts;
            }
            if (snap->memview->active_ooo_len > 0) {
                has_data = true;
                /* OOO is sorted in memview */
                if (snap->memview->active_ooo[0].ts < active_min)
                    active_min = snap->memview->active_ooo[0].ts;
                if (snap->memview->active_ooo[snap->memview->active_ooo_len - 1].ts > active_max)
                    active_max = snap->memview->active_ooo[snap->memview->active_ooo_len - 1].ts;
            }

            if (has_data && active_max >= t1 && active_min < t2) {
                tl_twoway_iter_t* it = NULL;
                st = tl_twoway_iter_create(alloc,
                                            snap->memview->active_run,
                                            snap->memview->active_run_len,
                                            snap->memview->active_ooo,
                                            snap->memview->active_ooo_len,
                                            t1, t2, &it);
                if (st != TL_OK) {
                    tl_qplan_destroy(plan);
                    return st;
                }

                if (tl_twoway_iter_state(it) == TL_ITER_READY) {
                    st = plan_add_iter(plan, &twoway_iter_vtable, it, component_id++);
                    if (st != TL_OK) {
                        tl_twoway_iter_destroy(it);
                        tl_qplan_destroy(plan);
                        return st;
                    }
                } else {
                    tl_twoway_iter_destroy(it);
                }
            }
        }

        /* Sealed memruns (each is a 2-way merge) */
        for (size_t i = 0; i < snap->memview->sealed_len; i++) {
            const tl_memrun_t* mr = snap->memview->sealed[i];
            if (!memrun_overlaps(mr, t1, t2)) continue;

            tl_twoway_iter_t* it = NULL;
            st = tl_twoway_iter_create(alloc,
                                        mr->run, mr->run_len,
                                        mr->ooo, mr->ooo_len,
                                        t1, t2, &it);
            if (st != TL_OK) {
                tl_qplan_destroy(plan);
                return st;
            }

            if (tl_twoway_iter_state(it) == TL_ITER_READY) {
                st = plan_add_iter(plan, &twoway_iter_vtable, it, component_id++);
                if (st != TL_OK) {
                    tl_twoway_iter_destroy(it);
                    tl_qplan_destroy(plan);
                    return st;
                }
            } else {
                tl_twoway_iter_destroy(it);
            }
        }
    }

    /* Build effective tombstones */
    tl_intervals_t tombs_intervals;
    st = collect_tombstones(alloc, snap, t1, t2, &tombs_intervals);
    if (st != TL_OK) {
        tl_qplan_destroy(plan);
        return st;
    }

    /* Convert to immutable tombstones */
    if (tl_intervals_len(&tombs_intervals) > 0) {
        st = tl_tombstones_create(alloc, &tombs_intervals, &plan->eff_tombs);
        tl_intervals_destroy(&tombs_intervals);
        if (st != TL_OK) {
            tl_qplan_destroy(plan);
            return st;
        }
    } else {
        tl_intervals_destroy(&tombs_intervals);
    }

    *out = plan;
    return TL_OK;
}

void tl_qplan_destroy(tl_qplan_t* plan) {
    if (plan == NULL) return;

    /* Destroy all component iterators */
    for (uint32_t i = 0; i < plan->n_iters; i++) {
        if (plan->iters[i].vtable != NULL && plan->iters[i].impl != NULL) {
            plan->iters[i].vtable->destroy(plan->iters[i].impl);
        }
    }
    if (plan->iters != NULL) {
        tl__free(plan->alloc, plan->iters);
    }

    /* Destroy effective tombstones */
    if (plan->eff_tombs != NULL) {
        tl_tombstones_destroy(plan->alloc, plan->eff_tombs);
    }

    tl__free(plan->alloc, plan);
}
