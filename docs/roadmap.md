# Roadmap (living, verbose)
Purpose: make it trivial for a new agent (or future me) to understand what we are doing, why, and in what order. Clarity beats brevity; uneven depth per section is fine as long as everything is accurate. No tables. Use tags like `[target YYYY-MM-DD]`, `[status TODO|IN-PROGRESS|DONE]`, `[owner Jörn]`, `[risk]`, `[depends]`.

## Conventions
- Each section is a phase with nested bullets; earlier bullets are prerequisites for later ones unless stated otherwise.
- Dates are anchors, not commitments; update when they drift.
- Status tags live inline next to the item.
- When scope changes, append a one-line rationale.
- Keep near-term items concrete; keep long-term items coarse.
- Link blockers explicitly; if a bullet is blocked, say so with `[depends]` or `[risk blocked-by ...]`.

---

## Immediate blocking items (must resolve before Phase B starts)
- Tolerances & numerics policy (eps, perturb/normalize rules, near-lagrangian cutoff, action/rotation slack). `[status TODO] [owner Jörn] [target 2025-12-03]` → deliver a short table (symbol, meaning, unit, default value) in `docs/numerics.md`; mirror constants in Rust/Python once set.
- Baseline polytope truth set: simplex, cube, crosspolytope, HK2024 counterexample (capacity/sys values). `[status TODO] [owner Jörn] [target 2025-12-03]` → table with value + citation + storage path (e.g., `packages/rust_viterbo/tests/baselines.json` and matching Python fixture).
- Sampler defaults + rejection thresholds (offset range, #halfspaces ranges for test/prod, near-lagrangian threshold, volume bounds). `[status TODO] [owner Jörn] [target 2025-12-05]` → define parameters, units, numeric ranges for test vs prod, stored in `packages/python_viterbo/data/configs/sampler.{test,prod}.json` with documented schema.
- Lean axiom list with sources (which lemmas are assumed vs proved). `[status TODO] [owner Jörn] [target 2025-12-05]` → list in `packages/lean_viterbo/AXIOMS.md` (name, statement, scope, source, future-proof plan).
- Canonical paths confirmation: figures under `packages/thesis/src/assets/figures/<chapter>/...`; configs under `packages/python_viterbo/data/configs/`. `[status TODO] [owner Jörn]` → decide policy for out-of-place files (move or symlink) and naming conventions.

Keep these documented in `docs/pm-knowledge-transfer.md`; once answered, copy the authoritative choices into specs/tests.

---

## Phase A – Specification (non-lagrangian first)
- Write the math-level algorithm spec covering non-lagrangian 2-faces only. Include notation, required lemmas, and numerics policy (eps, perturb/normalize rules).  
  - `[target 2025-12-03] [status TODO] [owner Jörn]`
  - Output: MDX/Markdown spec in repo (prefer `packages/thesis/src/01-algorithm.mdx` section or `docs/algorithm-spec.md`) with sections: assumptions, algorithm steps, numerics, failure modes.
- Review + freeze the spec for implementation.  
  - `[target 2025-12-05] [status TODO] [owner Jörn] [depends Phase A first bullet]`
  - Output: accepted tolerance table; list of open questions deferred to later phases.
  - Blockers: tolerances, baseline truth set, sampler defaults, Lean axiom list (see “Immediate blocking items”).

## Phase B – Implementation in lockstep (Rust / Python / Lean)
- Rust core skeleton for non-lagrangian case. H/V reps, skeleton builder, search scaffolding; unit tests on baseline polytopes.  
  - `[target 2025-12-10] [status TODO]`
  - Deliverables: reusable polytope types (H/V reps, skeleton) in `packages/rust_viterbo/geom` (or dedicated crate if split), branch-and-bound scaffolding, baseline tests using confirmed capacities/sys values.
- Python glue + integration smoke via maturin module.  
  - `[target 2025-12-12] [status TODO] [depends Rust skeleton]`
  - Deliverables: maturin build, thin CLI/runner (`viterbo.cli` or `scripts/`—decide), one integration test (e.g., `packages/python_viterbo/tests/test_integration.py`) that loads 1–2 polytopes and calls Rust.
- Lean alignment: axioms/stubs that mirror the spec; avoid `sorry` except where explicitly marked “axiom”; names and sources recorded.  
  - `[target 2025-12-17] [status TODO]`
  - Deliverables: named axioms with citations (`AXIOMS.md`), mapping doc Rust type → Lean structure, theorem stubs aligned with API shapes; minimal runnable = `lake build` succeeds and a tiny example lemma type-checks.
- Cross-sync pass: ensure spec ↔ Rust ↔ Python ↔ Lean match; update comments/docs accordingly.  
  - `[target 2025-12-20] [status TODO]`
  - Deliverables: changelog of any interface/notation adjustments in `CHANGELOG.md` (or section in roadmap); doc comments updated in all three implementations (Rust docstrings, Python docstrings, Lean module doc).

## Phase C – Validation & visibility
- Baseline correctness and perf visibility. Plots for known polytopes; profiling on HK2024 case; document findings.  
  - `[target 2025-12-22] [status TODO]`
  - Deliverables: correctness plots (matplotlib/plotly script path recorded), perf profile (wall time, node expansions, pruning hits, tolerance-trigger counts) on HK2024; short note on hotspots; artifacts stored under `packages/thesis/src/assets/figures/perf/...` (or shared store if large).
- Ablation + instrumentation results (e.g., pruning heuristics, ordering). Record what helps/hurts.  
  - `[target 2026-01-05] [status TODO] [depends previous bullet]`
  - Deliverables: ablation table + narrative; recommendation on default heuristics; store results + script command used.

## Phase D – Experiments ramp
- Samplers + small test dataset + figure pipeline wired into thesis/docs-site. Configs checked in; figures visible.  
  - `[target 2026-01-12] [status TODO]`
  - Deliverables: test dataset (≤LFS threshold; otherwise git-lfs), configs in `packages/python_viterbo/data/configs/` with schema tests, figure assets in thesis path, snapshot tests for schema/figures; regenerate command recorded.
- Large dataset run (10^6-scale or chosen size) with schema regression guards; stored via git-lfs or shared store.  
  - `[target 2026-01-26] [status TODO] [risk runtime/cost]`
  - Deliverables: production dataset with schema checks; storage location documented (git-lfs vs `/workspaces/worktrees/shared/...`), rerun command recorded; size threshold policy stated (e.g., >50MB → LFS/shared).

## Phase E – Thesis freeze window
- Code freeze for thesis; doc polish only.  
  - `[target 2026-02-15] [status TODO] [risk schedule drift]`
- Submission.  
  - `[target 2026-03-??] [status TODO]`
  - Deliverables: PDF + site RC; freeze notice; checklist of what changed post-freeze (ideally none); define freeze branch/tag and allowed exceptions (if any).

---

## Working notes / decisions
- Start with non-lagrangian-only algorithm to avoid numerical instability; near-lagrangian handling may come later (perturb-and-approx vs bespoke handling).
- Keep Rust/Lean/Python/Thesis in sync; any change to one requires at least a note or matching tweak in the others.
- Tests: baseline polytopes (simplex, cube, crosspolytope, HK2024, etc.) must be codified once capacities/sys ratios are confirmed.
- Experiments must be scripted (config-driven) and reproducible; artifacts stored via git-lfs or shared store with commit provenance.
- Agentctl reliability is currently a risk (session discovery confusion, missing `final_message.txt`). Track via issues #6 and #7; avoid relying on `agentctl start` for critical tasks until fixed.
- Prefer `gh ... --body-file` (never `--body`) to avoid shell escaping problems when filing issues/PRs.

## Update workflow
- Weekly (Mondays): refresh statuses, slide dates if needed, append rationale for changes. `[owner Jörn]` Record rationale in this file under the relevant bullet.
- When adding a new phase item: include `[target] [status] [owner] [depends]` tags.
- Link to related GitHub issues when risks are mentioned (e.g., agentctl issues #6, #7).
