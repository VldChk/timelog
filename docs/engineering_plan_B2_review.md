# Review: engineering_plan_B2_pytimelog.md + engineering_plan_B2_errata.md vs B2 LLD/HLD and current core

## Findings (ordered by severity)

### High
- Delete APIs treat TL_EBUSY as failure even though tombstone insert already succeeded; callers can retry and create duplicate tombstones or mis-handle success. Evidence: `docs/engineering_plan_B2_pytimelog.md:760`, `include/timelog/timelog.h:290`, `src/tl_timelog.c:698`, `src/tl_timelog.c:732`.
- LLD-B2 still specifies rollback/auto-flush on TL_EBUSY, conflicting with the errata-integrated plan (EBUSY == success, no retry); this spec conflict must be resolved. Evidence: `docs/timelog_v1_lld_B2_pytimelog_engine_wrapper.md:373`, `docs/timelog_v1_lld_B2_pytimelog_engine_wrapper.md:379`, `docs/engineering_plan_B2_pytimelog.md:557`.

### Medium
- busy_policy parsing/validation is unspecified: busy_policy_str is parsed but no mapping/default to self->busy_policy is described in init, leaving behavior undefined. Evidence: `docs/engineering_plan_B2_pytimelog.md:389`, `docs/engineering_plan_B2_pytimelog.md:431`, `docs/engineering_plan_B2_pytimelog.md:319`.
- TL_PY_BUSY_FLUSH is defined but extend() does not execute a flush on EBUSY, so policy semantics differ between append and extend. Evidence: `docs/engineering_plan_B2_pytimelog.md:299`, `docs/engineering_plan_B2_pytimelog.md:721`.
- delete_range rejects t1 == t2, but core allows empty range as a no-op and LLD-B2 calls for that behavior. Evidence: `docs/engineering_plan_B2_pytimelog.md:756`, `docs/timelog_v1_lld_B2_pytimelog_engine_wrapper.md:313`, `src/tl_timelog.c:685`.
- delete_before has no implementation spec even though it appears in tests and the method table, leaving behavior ambiguous. Evidence: `docs/engineering_plan_B2_pytimelog.md:143`, `docs/engineering_plan_B2_pytimelog.md:940`.
- compact() references run_maintenance(), but there is no method spec or method table entry for it, leaving manual-mode compaction undefined. Evidence: `docs/engineering_plan_B2_pytimelog.md:863`, `docs/engineering_plan_B2_pytimelog.md:926`, `docs/engineering_plan_B2_errata.md:400`.

### Low
- Close debug warning uses tl_stats_quick, which is not declared in the core API; this will not compile unless a new API is added. Evidence: `docs/engineering_plan_B2_pytimelog.md:1161`, `docs/engineering_plan_B2_errata.md:507`, `include/timelog/timelog.h:474`.
- drain_batch_limit defaults to -1 but is passed directly into tl_py_handle_ctx_init (uint32_t, 0 = unlimited); map -1 to 0 explicitly to avoid implicit UINT32_MAX. Evidence: `docs/engineering_plan_B2_pytimelog.md:398`, `docs/engineering_plan_B2_pytimelog.md:426`, `bindings/cpython/include/timelogpy/py_handle.h:143`.

## Open questions / assumptions
- Should TL_EBUSY handling for delete_range/delete_before mirror append (success with backpressure) and, if so, should busy_policy apply to deletes?
- Is the extension module intended to be package-qualified (timelog._timelog) or top-level (_timelog)? This affects PyModuleDef.m_name vs tp_name and error names. Evidence: `docs/engineering_plan_B2_pytimelog.md:337`, `docs/engineering_plan_B2_pytimelog.md:981`, `bindings/cpython/src/py_errors.c:46`.
- HLD still shows on_drop acquiring the GIL and DECREF inline; confirm if HLD will be updated to match the no-Python-C-API-in-on_drop constraint. Evidence: `docs/timelog_python_north_star_hld.md:238`.

## Alignment highlights (non-blocking)
- Errata-integrated plan now treats TL_EBUSY for append/extend as success with no retry, matching core semantics and avoiding UAF/duplicate inserts. Evidence: `docs/engineering_plan_B2_pytimelog.md:557`, `src/tl_timelog.c:568`.

## Sources reviewed
- `docs/engineering_plan_B2_errata.md`
- `docs/engineering_plan_B2_pytimelog.md`
- `docs/timelog_v1_lld_B2_pytimelog_engine_wrapper.md`
- `docs/timelog_python_north_star_hld.md`
- `include/timelog/timelog.h`
- `src/tl_timelog.c`
- `bindings/cpython/include/timelogpy/py_handle.h`
- `bindings/cpython/src/py_errors.c`
