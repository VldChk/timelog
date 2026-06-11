# Timelog Creativity Lab

> **Mission:** Mine the raw idea-heap in `.ideas/` for everything that could make Timelog
> a better, more reliable, more performant, best-in-the-world time-index for Python — then
> *actually build, measure, and seed* the promising ones in isolated labs.
>
> Open mind of a scientist; evidence before assertions.

**Branch:** `timelog-experiments` @ `e7e7efb` (merged 1.2.0 baseline).
**Input:** `.ideas/` — 37 GPT-style explainer/primer docs (gitignored, local-only; the
source corpus is not reproduced in this deliverable).
**Home:** `ideas-lab/` (distinct from the pre-existing `lab/` resilience suite — that is untouched).

---

## Method (8 phases, mirrors the brief)

| # | Phase | Output | Status |
|---|-------|--------|--------|
| 0 | Orient: enumerate, hash, exact-dedup | exact-dup map (3 pairs) | ✅ done |
| 1 | Digest every unique doc → structured idea atoms (12-agent fan-out, 176 atoms) | `00-raw-catalog.md` | ✅ done |
| 2 | Semantic dedup + relevance filter + theme grouping | `01-themes.md` | ✅ done |
| 3 | Exhaustive per-theme idea registry (8 themes) | `01-themes.md` | ✅ done |
| 4 | My own ideas + web/PEP research (5 strands, 40 findings/30 ideas/25 corrections) | `02-ideation.md` | ✅ done |
| 5 | Tractability triage → exploration shortlist | `03-classification.md` | ✅ done |
| 6 | Build MVPs in worktrees/labs, measure (**phase-one + serious-audit experiments**) | `experiments/*/RESULT.md`, `FLEET_RESULTS.md` | ✅ done |
| 7 | Seed/classify: not-for-us / worth-productionizing / major-refactor + final report | `03-classification.md`, `AUDIT_REPORT.md` | ✅ done |

**▶ Start here: [`AUDIT_REPORT.md`](AUDIT_REPORT.md)** — the current final seed. `REPORT.md` is the
phase-one report and is intentionally kept as historical context. Headline results and candidates:
facade-`append` fold **3.46×** (exp06), strict typed-buffer `bulk_append` **9–10×** vs per-append (C2),
`METH_FASTCALL` append −23.7%/point −15.8% (exp01), branchless `lower_bound` point −15.2% / 3–5× search
(exp02), Arrow/DLPack zero-copy interop as medium feature work (C3), compaction studied + the adversarial-OOO
**5.3×** read lever and workload-sensitive delete reclaim gap (C4/C5); loser-tree, SoA catalog, and modern
disk-LSM strategies were killed or rejected by measurement/research.

Current evidence caveat: C2/C3 preserve prototype patches and prior-run reported numbers, but not raw
benchmark/test transcripts in this tree. Treat them as high-value rerun candidates before production PRs.
Source-corpus caveat: because `.ideas/` remains private/local, reviewers can audit the saved digests and
classification artifacts but cannot independently re-read the original source documents from this tree.

## Exact-duplicate map (Phase 0)

Confirmed by md5 — 37 files → **34 unique**:
- `doc_7 ≡ doc_19`
- `doc_12 ≡ doc_23`
- `doc_13 ≡ doc_25`

Canonical kept: `doc_7`, `doc_12`, `doc_13`. Dropped dups: `doc_19`, `doc_23`, `doc_25`.

## Seeding rubric (Phase 7)

Every surviving idea family gets one verdict, with evidence:
- 🟥 **BS / not-for-us** — wrong stack, no transfer, or measured net-negative.
- 🟩 **Worth productionizing next** — real measured win or cheap hardening with clear production scope.
- 🟦 **Cool-but-costly** — genuine upside but needs major refactor / new subsystem.
- ⬛ **Inconclusive** — promising but needs more than an MVP to decide.

---

*This README is the living index. Each phase appends its artifact link above.*
