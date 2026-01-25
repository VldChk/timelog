#include "tl_submerge.h"
#include <string.h>

tl_status_t tl_submerge_init(tl_submerge_t* sm,
                              tl_alloc_ctx_t* alloc,
                              size_t src_count) {
    TL_ASSERT(sm != NULL);
    TL_ASSERT(alloc != NULL);

    memset(sm, 0, sizeof(*sm));
    sm->alloc = alloc;
    tl_heap_init(&sm->heap, alloc);

    if (src_count == 0) {
        return TL_OK;
    }

    if (src_count > SIZE_MAX / sizeof(tl_subsrc_t)) {
        return TL_EOVERFLOW;
    }

    sm->srcs = tl__malloc(alloc, src_count * sizeof(tl_subsrc_t));
    if (sm->srcs == NULL) {
        tl_heap_destroy(&sm->heap);
        return TL_ENOMEM;
    }

    memset(sm->srcs, 0, src_count * sizeof(tl_subsrc_t));
    sm->src_count = src_count;
    return TL_OK;
}

void tl_submerge_destroy(tl_submerge_t* sm) {
    if (sm == NULL) {
        return;
    }

    if (sm->srcs != NULL) {
        tl__free(sm->alloc, sm->srcs);
        sm->srcs = NULL;
    }
    sm->src_count = 0;

    tl_heap_destroy(&sm->heap);
    sm->alloc = NULL;
}

tl_status_t tl_submerge_build(tl_submerge_t* sm) {
    TL_ASSERT(sm != NULL);

    tl_heap_clear(&sm->heap);

    if (sm->src_count == 0) {
        return TL_OK;
    }

    tl_status_t st = tl_heap_reserve(&sm->heap, sm->src_count);
    if (st != TL_OK) {
        return st;
    }

    for (size_t i = 0; i < sm->src_count; i++) {
        tl_subsrc_t* src = &sm->srcs[i];
        if (src->len > 0 && src->data == NULL) {
            return TL_EINVAL;
        }
        if (src->pos >= src->end) {
            continue;
        }

        const tl_record_t* rec = &src->data[src->pos++];
        tl_heap_entry_t entry = {
            .ts = rec->ts,
            .component_id = src->tie_id,
            .handle = rec->handle,
            .iter = src
        };
        st = tl_heap_push(&sm->heap, &entry);
        if (st != TL_OK) {
            tl_heap_clear(&sm->heap);
            return st;
        }
    }

    return TL_OK;
}

tl_status_t tl_submerge_next(tl_submerge_t* sm, tl_record_t* out) {
    TL_ASSERT(sm != NULL);

    const tl_heap_entry_t* peek = tl_heap_peek(&sm->heap);
    if (peek == NULL) {
        return TL_EOF;
    }

    if (out != NULL) {
        out->ts = peek->ts;
        out->handle = peek->handle;
    }

    tl_subsrc_t* src = (tl_subsrc_t*)peek->iter;
    uint32_t component_id = peek->component_id;

    if (src->pos < src->end) {
        const tl_record_t* rec = &src->data[src->pos++];
        tl_heap_entry_t entry = {
            .ts = rec->ts,
            .component_id = component_id,
            .handle = rec->handle,
            .iter = src
        };
        tl_heap_replace_top(&sm->heap, &entry);
    } else {
        tl_heap_entry_t discard;
        (void)tl_heap_pop(&sm->heap, &discard);
    }

    return TL_OK;
}

void tl_submerge_seek(tl_submerge_t* sm, tl_ts_t target) {
    TL_ASSERT(sm != NULL);

    if (tl_heap_is_empty(&sm->heap)) {
        return;
    }

    const tl_heap_entry_t* min = tl_heap_peek(&sm->heap);
    if (min != NULL && min->ts >= target) {
        return;
    }

    while (!tl_heap_is_empty(&sm->heap)) {
        const tl_heap_entry_t* entry = tl_heap_peek(&sm->heap);
        if (entry->ts >= target) {
            break;
        }

        tl_heap_entry_t popped;
        (void)tl_heap_pop(&sm->heap, &popped);

        tl_subsrc_t* src = (tl_subsrc_t*)popped.iter;
        size_t new_pos = tl_submerge_lower_bound(src->data, src->end, target);
        if (new_pos > src->pos) {
            src->pos = new_pos;
        }

        if (src->pos >= src->end) {
            continue;
        }

        const tl_record_t* rec = &src->data[src->pos++];
        tl_heap_entry_t new_entry = {
            .ts = rec->ts,
            .component_id = popped.component_id,
            .handle = rec->handle,
            .iter = src
        };
        tl_status_t st = tl_heap_push(&sm->heap, &new_entry);
        TL_ASSERT(st == TL_OK);
    }
}
