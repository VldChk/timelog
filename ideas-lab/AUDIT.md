# Timelog Serious Audit — Charter & Progress Tracker

> **Reset (2026-06-04):** the first pass cherry-picked one-file wins and "analytically analyzed" the hard
> themes. This is the real audit: **every large theme gets a real prototype, built in isolation, measured
> rigorously, and seeded by evidence** — not classified from research. No rush; correctness over speed.

## Isolation & reversibility contract (non-negotiable)

1. **Baseline `e7e7efb` (branch `timelog-experiments`) is never modified.** Every experiment branches off it.
2. **One git worktree + branch per experiment:** `git worktree add -b exp2/<theme>-<id> ../tl-wt-<id> e7e7efb`.
   The main checkout's working tree is never touched by an experiment build.
3. **Each worktree builds in its own `build-rel/`** and stages its own `_timelog*.so`. Benchmarks run with
   `PYTHONPATH=<worktree>/python`. No cross-contamination.
4. **Every experiment is reversible:** `git worktree remove <path>` + `git branch -D exp2/<id>` discards it
   with zero trace on the baseline. Patches are also saved under `experiments/<id>/`.
5. **Correctness gate before any verdict:** the worktree must pass the relevant suite (core `test_timelog`
   480/480, and/or facade pytest 98+) — a perf change that breaks a test is a 🟥 regardless of speed.
6. **Measurement protocol** (from the methodology review, `_data/compaction-study.json`): subprocess per
   knob-cell where it matters, ≥3–5 paired-seed repeats, pinned core, gc-controlled, `thread_time_ns` for
   attributable CPU, `/proc/self/statm` RSS at quiescence. Report median + spread, not single shots.

## Theme roster — real experiments (status: ⬜ todo · 🔨 building · 📊 measuring · ✅ seeded)

### T4 — Compaction (flagship: build *all* related ideas, not one)
| id | experiment | kind | status |
|----|-----------|------|--------|
| C4-harness | Configurable compaction-experiment harness (workloads × knobs → WA/SA/read-amp/CPU/RSS) | infra | ✅ `harness/compaction_lab.py` + `run_matrix.py` |
| C4-knobs | Full knob sweep (max_delta_segments × workloads, 3 seeds) | measure | ✅ `KNOB_MATRIX.md` (WA 28× swing, reads flat on mild workloads, adaptive-trigger seed) |
| C4-wwd | Whole-window drop | C build | ✅ 🟦 built+480-gated+re-verified; 67–275× pure-C TTL, wash in CPython; review found false-negative |
| C4-gran | Granular per-window compaction (RAM transient) | C build | ✅ harnessed; existing max_compaction_windows cap is insufficient for wide-OOO RSS and costs repeated L1 re-merges |
| C4-roi | Adaptive compaction decision (trigger by OOO-overlap / ROI) prototype | C build | ⬜ (seeded by C4-knobs) |
| C4-qskip | Query-time window skip for L1 windows outside `[t1,t2)` (verify/implement) | C build | ⬜ |

### T3 — Zero-copy interop (build the real export surfaces)
| C3-arrow | `__arrow_c_array__` on PageSpan, zero-copy to Polars/PyArrow | C build | ✅ 🟦 patch-only provenance in current tree; prior run reported zero-copy; rerun/save logs before PR |
| C3-dlpack | `__dlpack__`/`__dlpack_device__` on PageSpan → numpy/torch zero-copy | C build | ✅ 🟦 patch-only provenance in current tree; prior run reported zero-copy; rerun/save logs before PR |

### T5 — Tombstones / deletes
| C5-canon | Tombstone/delete reclaim sweep | measure | ✅ 🟦 GAP: retention-shaped 50% delete reclaims 0 space in lab; spot cases can reclaim, so default-disabled/workload-sensitive L1 reclaim coverage/design needed |
| C5-reclaim | Physical reclaim (ties to C4-wwd) | measure | ✅ folded into C5-canon: no reclaim until new writes trigger compaction |

### T6 — Free-threading hardening (real, under TSan/3.14t)
| C6-exports | PageSpan `exports` counter FT safety | C build | ✅ already-hardened (under CS); verified on 3.14t (0 crashes) |
| C6-cs | Critical-section blocking audit | audit | ✅ sound — iter CS wraps lock-free tl_iter_next; no footgun |

### T7 — Memory / allocator (build the harness, measure)
| C7-mem | RSS probe + allocator A/B | infra+measure | ✅ 🟦 87% RSS native; mimalloc −12% peak/−37% frag (−2% steady) |

### T2 — Batch ingest (close the headroom found)
| C2-bulk | Typed-buffer `bulk_append(int64_ts_buffer, objects)` zero-unpack path | C build | ✅ 🟩 patch-only provenance in current tree; prior run reported 9–10× vs per-append; endian fix + rerun logs required |

### T1 — Binding (already built; productionize)
| C1-fold | Productionize facade-fold (all 3 signatures, configured time_unit, METH_FASTCALL\|KEYWORDS) | C build | ✅(MVP exp06) |

## Phase-1 quick experiments (the first pass — kept, now superseded by the above)
exp01 FASTCALL ✅ · exp02 branchless ✅ · exp03 competitive ✅ · exp04 compaction (measured, additions
NOW being built) · exp05 loser-tree 🟥 · exp06 facade-fold ✅(MVP).

---
*Progress is tracked by the status column above; each ✅ links to `experiments/<id>/RESULT.md` with the
built code, the measurement, and the evidence-based seed.*
