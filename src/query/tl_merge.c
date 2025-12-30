#include "../internal/tl_merge.h"
#include <string.h>

/*
 * Heap comparator: compare by (timestamp, component_id).
 * Returns true if a should come before b (a < b).
 */
static bool heap_less(const tl_merge_node_t* a, const tl_merge_node_t* b) {
    if (a->record.ts != b->record.ts) {
        return a->record.ts < b->record.ts;
    }
    return a->component_id < b->component_id;
}

/*
 * Swap two heap nodes.
 */
static void heap_swap(tl_merge_node_t* a, tl_merge_node_t* b) {
    tl_merge_node_t tmp = *a;
    *a = *b;
    *b = tmp;
}

/*
 * Sift up (after insertion).
 */
static void heap_sift_up(tl_merge_node_t* heap, uint32_t idx) {
    while (idx > 0) {
        uint32_t parent = (idx - 1) / 2;
        if (heap_less(&heap[idx], &heap[parent])) {
            heap_swap(&heap[idx], &heap[parent]);
            idx = parent;
        } else {
            break;
        }
    }
}

/*
 * Sift down (after extraction or update).
 */
static void heap_sift_down(tl_merge_node_t* heap, uint32_t size, uint32_t idx) {
    while (true) {
        uint32_t smallest = idx;
        uint32_t left = 2 * idx + 1;
        uint32_t right = 2 * idx + 2;

        if (left < size && heap_less(&heap[left], &heap[smallest])) {
            smallest = left;
        }
        if (right < size && heap_less(&heap[right], &heap[smallest])) {
            smallest = right;
        }

        if (smallest != idx) {
            heap_swap(&heap[idx], &heap[smallest]);
            idx = smallest;
        } else {
            break;
        }
    }
}

/*
 * Push a node onto the heap.
 */
static void heap_push(tl_merge_node_t* heap, uint32_t* size, const tl_merge_node_t* node) {
    heap[*size] = *node;
    heap_sift_up(heap, *size);
    (*size)++;
}

/*
 * Pop the minimum node from the heap.
 */
static void heap_pop(tl_merge_node_t* heap, uint32_t* size) {
    if (*size == 0) return;
    (*size)--;
    if (*size > 0) {
        heap[0] = heap[*size];
        heap_sift_down(heap, *size, 0);
    }
}

/*
 * Build heap from component iterators.
 */
static tl_status_t build_heap(tl_merge_iter_t* it) {
    it->heap_size = 0;

    if (it->plan == NULL) {
        it->state = TL_ITER_EOF;
        return TL_OK;
    }

    for (uint32_t i = 0; i < it->plan->n_iters; i++) {
        tl_component_iter_t* comp = &it->plan->iters[i];

        tl_iter_state_t state = comp->vtable->state(comp->impl);
        if (state != TL_ITER_READY) continue;

        const tl_record_t* rec = comp->vtable->peek(comp->impl);
        if (rec == NULL) continue;

        tl_merge_node_t node;
        node.record = *rec;
        node.iter = comp;
        node.component_id = comp->component_id;

        heap_push(it->heap, &it->heap_size, &node);
    }

    if (it->heap_size > 0) {
        it->current = it->heap[0].record;
        it->state = TL_ITER_READY;
    } else {
        it->state = TL_ITER_EOF;
    }

    return TL_OK;
}

tl_status_t tl_merge_iter_create(const tl_allocator_t* alloc,
                                  tl_qplan_t* plan,
                                  tl_merge_iter_t** out) {
    if (out == NULL) return TL_EINVAL;
    *out = NULL;

    tl_merge_iter_t* it = tl__calloc(alloc, 1, sizeof(tl_merge_iter_t));
    if (it == NULL) return TL_ENOMEM;

    it->alloc = alloc;
    it->plan = plan;
    it->state = TL_ITER_EOF;

    /* Allocate heap */
    uint32_t n_iters = plan ? plan->n_iters : 0;
    if (n_iters > 0) {
        it->heap = tl__malloc(alloc, n_iters * sizeof(tl_merge_node_t));
        if (it->heap == NULL) {
            tl__free(alloc, it);
            return TL_ENOMEM;
        }
        it->heap_cap = n_iters;

        /* Build initial heap */
        build_heap(it);
    }

    *out = it;
    return TL_OK;
}

void tl_merge_iter_destroy(tl_merge_iter_t* it) {
    if (it == NULL) return;

    if (it->heap != NULL) {
        tl__free(it->alloc, it->heap);
    }

    tl__free(it->alloc, it);
}

const tl_record_t* tl_merge_iter_peek(tl_merge_iter_t* it) {
    if (it == NULL || it->state != TL_ITER_READY) return NULL;
    return &it->current;
}

tl_status_t tl_merge_iter_advance(tl_merge_iter_t* it) {
    if (it == NULL) return TL_EINVAL;
    if (it->state != TL_ITER_READY || it->heap_size == 0) {
        it->state = TL_ITER_EOF;
        return TL_EOF;
    }

    /* Get the iterator that produced current minimum */
    tl_component_iter_t* min_iter = it->heap[0].iter;

    /* Advance that iterator */
    tl_status_t st = min_iter->vtable->advance(min_iter->impl);

    if (st == TL_OK) {
        /* Update heap with new record */
        const tl_record_t* rec = min_iter->vtable->peek(min_iter->impl);
        if (rec != NULL) {
            it->heap[0].record = *rec;
            heap_sift_down(it->heap, it->heap_size, 0);
        } else {
            /* Iterator exhausted (shouldn't happen if advance returned OK) */
            heap_pop(it->heap, &it->heap_size);
        }
    } else {
        /* Iterator exhausted */
        heap_pop(it->heap, &it->heap_size);
    }

    /* Update current */
    if (it->heap_size > 0) {
        it->current = it->heap[0].record;
        return TL_OK;
    } else {
        it->state = TL_ITER_EOF;
        return TL_EOF;
    }
}

tl_iter_state_t tl_merge_iter_state(tl_merge_iter_t* it) {
    return it ? it->state : TL_ITER_EOF;
}

tl_status_t tl_merge_iter_seek(tl_merge_iter_t* it, tl_ts_t ts) {
    if (it == NULL || it->plan == NULL) return TL_EINVAL;

    /* Seek all component iterators */
    for (uint32_t i = 0; i < it->plan->n_iters; i++) {
        tl_component_iter_t* comp = &it->plan->iters[i];
        if (comp->vtable->seek != NULL) {
            comp->vtable->seek(comp->impl, ts);
        }
    }

    /* Rebuild heap */
    build_heap(it);

    return (it->state == TL_ITER_READY) ? TL_OK : TL_EOF;
}
