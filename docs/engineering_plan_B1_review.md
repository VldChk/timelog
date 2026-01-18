# Review: engineering_plan_B1.md vs Python HLD/LLD and current C core

## Findings (ordered by severity)

### Critical
- Close-time reclamation gap: the plan relies on "flush() before close" but the core does not call on_drop during tl_close, and tombstone-filtered iterators cannot see logically deleted records, so engine-owned refs can leak at close (including tombstoned records and any records at TL_TS_MAX). Evidence: `docs/engineering_plan_B1.md:267` `docs/timelog_v1_lld_B1_python_handle_lifetime.md:368` `include/timelog/timelog.h:272` `src/tl_timelog.c:447` `src/maint/tl_compaction.c:1247` `src/tl_timelog.c:1159`.

### High
- Spec mismatch on on_drop behavior: the Python HLD shows on_drop acquiring the GIL and DECREFing inline, while the LLD-B1 and the plan forbid any Python C-API in on_drop; this is a contract conflict that must be resolved before implementation. Evidence: `docs/timelog_python_north_star_hld.md:238` `docs/timelog_python_north_star_hld.md:242` `docs/timelog_python_north_star_hld.md:528` `docs/timelog_v1_lld_B1_python_handle_lifetime.md:75` `docs/engineering_plan_B1.md:217` `docs/engineering_plan_B1.md:556`.
- Manual-mode compaction semantics are easy to mis-implement: `tl_compact()` is a request only, so Python `compact()` will be a no-op unless the binding explicitly runs `tl_maint_step`; tests expecting reclamation after compact will fail in manual mode. Evidence: `include/timelog/timelog.h:315` `src/tl_timelog.c:1052`.

### Medium
- Batch append rollback is unsafe with `tl_append_batch`: partial inserts can succeed without returning a count, so pre-INCREFing a whole batch cannot be rolled back correctly; the binding must implement per-element append (or add a new core API that reports inserted count). Evidence: `src/delta/tl_memtable.h:137` `src/delta/tl_memtable.h:142` `docs/timelog_python_north_star_hld.md:285`.

### Low
- Non-atomic metrics in on_drop: `alloc_failures++` is documented as non-atomic in a potentially multi-threaded callback, which is a data race in C; make it atomic or thread-local even if it is "just metrics". Evidence: `docs/engineering_plan_B1.md:507`.
- Internal plan tension: the plan notes GIL acquisition in on_drop is safe due to lock ordering, but the same plan forbids Python C-API in on_drop; clarify to avoid implementation drift. Evidence: `docs/engineering_plan_B1.md:72` `docs/engineering_plan_B1.md:556`.

## Alignment highlights (non-blocking)
- on_drop callbacks are deferred until after successful publish in the core, matching the LLD-B1 retire -> quiesce -> release model. Evidence: `src/maint/tl_compaction.c:1247` `docs/engineering_plan_B1.md:27`.
- Pin tracking around snapshot acquire/release aligns with core snapshot semantics. Evidence: `docs/engineering_plan_B1.md:51` `docs/engineering_plan_B1.md:53` `docs/timelog_v1_lld_B1_python_handle_lifetime.md:311`.

## Open questions to resolve before implementation
- Do we add a core-level teardown hook (or raw iterator) so close can release all remaining handles, including tombstoned records? Evidence: `docs/timelog_v1_lld_B1_python_handle_lifetime.md:380`.
- If manual maintenance mode is supported in Python, what is the exact `compact()` contract (request-only vs run-to-quiescence)? Evidence: `include/timelog/timelog.h:315`.

## Sources reviewed
- `docs/timelog_python_north_star_hld.md`
- `docs/timelog_v1_lld_B1_python_handle_lifetime.md`
- `docs/engineering_plan_B1.md`
- `include/timelog/timelog.h`
- `src/tl_timelog.c`
- `src/maint/tl_compaction.c`
- `src/delta/tl_memtable.h`