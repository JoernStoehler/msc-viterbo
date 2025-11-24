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
- Tolerances & numerics policy (eps, perturb/normalize rules, near-lagrangian cutoff, action/rotation slack). `[status TODO] [owner Jörn] [target 2025-12-03]` → fill `docs/numerics.md` with a table (symbol, meaning, units, default, usage step, code const name) and point to Rust/Python constant paths.
- Baseline polytope truth set: simplex, cube, crosspolytope, HK2024 counterexample (capacity/sys values). `[status TODO] [owner Jörn] [target 2025-12-03]` → table (polytope definition/coords/scale, c_EHZ, sys, citation, expected error tolerance) stored at `packages/rust_viterbo/tests/baselines.json` + Python fixture; note canonical coordinate normalization.
- Sampler defaults + rejection thresholds (offset range, #halfspaces ranges for test/prod, near-lagrangian threshold, volume bounds, seed policy, rejection order). `[status TODO] [owner Jörn] [target 2025-12-05]` → JSON schema + defaults in `packages/python_viterbo/data/configs/sampler.{test,prod}.json`; document units and bounds.
- Lean axiom list with sources (which lemmas are assumed vs proved). `[status TODO] [owner Jörn] [target 2025-12-05]` → `packages/lean_viterbo/AXIOMS.md` listing name, statement, namespace, scope, source/citation, future-proof plan; reference guidelines for where axioms may be used.
- Canonical paths confirmation: figures under `packages/thesis/src/assets/figures/<chapter>/...`; configs under `packages/python_viterbo/data/configs/`. `[status TODO] [owner Jörn]` → policy: move out-of-place files into these paths; naming convention `<figure-id>.(json|png)`; configs kebab-case `.json`.

Keep these documented in `docs/pm-knowledge-transfer.md`; once answered, copy the authoritative choices into specs/tests.

---

## Phase A – Specification (non-lagrangian first)
- Write the math-level algorithm spec covering non-lagrangian 2-faces only. Include notation, required lemmas, and numerics policy (eps, perturb/normalize rules).  
  - `[target 2025-12-03] [status TODO] [owner Jörn]`
  - Output: MDX/Markdown spec in repo (prefer `packages/thesis/src/01-algorithm.mdx` section or `docs/algorithm-spec.md`) with sections: assumptions, definition of non-lagrangian 2-faces + detection test, required lemmas, algorithm steps, numerics, failure modes.
- Review + freeze the spec for implementation.  
  - `[target 2025-12-05] [status TODO] [owner Jörn] [depends Phase A first bullet]`
  - Output: accepted tolerance table; list of open questions deferred to later phases.
  - Blockers: tolerances, baseline truth set, sampler defaults, Lean axiom list (see “Immediate blocking items”).

## Phase B – Implementation in lockstep (Rust / Python / Lean)
- Rust core skeleton for non-lagrangian case. H/V reps, skeleton builder, search scaffolding; unit tests on baseline polytopes.  
  - `[target 2025-12-10] [status TODO]`
  - Deliverables: reusable polytope types (H/V reps, skeleton) in `packages/rust_viterbo/geom` (or dedicated crate if split), branch-and-bound scaffolding with stated ordering/heuristics/threading policy, baseline tests using confirmed capacities/sys values (fixtures path).
- Python glue + integration smoke via maturin module.  
  - `[target 2025-12-12] [status TODO] [depends Rust skeleton]`
  - Deliverables: maturin build, thin CLI/runner (`viterbo.cli` or `scripts/`—decide), expected CLI args/config format, one integration test (`packages/python_viterbo/tests/test_integration.py`) using sample polytopes fixture.
- Lean alignment: axioms/stubs that mirror the spec; avoid `sorry` except where explicitly marked “axiom”; names and sources recorded.  
  - `[target 2025-12-17] [status TODO]`
  - Deliverables: named axioms with citations (`AXIOMS.md`), mapping doc Rust type → Lean structure + module/namespace layout, theorem stubs aligned with API shapes; minimal runnable = `lake build` succeeds and a tiny example lemma (topic TBD) type-checks.
- Cross-sync pass: ensure spec ↔ Rust ↔ Python ↔ Lean match; update comments/docs accordingly.  
  - `[target 2025-12-20] [status TODO]`
  - Deliverables: changelog of any interface/notation adjustments in `CHANGELOG.md` (or section in roadmap); doc comments updated in all three implementations (Rust docstrings, Python docstrings, Lean module doc).

## Phase C – Validation & visibility
- Baseline correctness and perf visibility. Plots for known polytopes; profiling on HK2024 case; document findings.  
  - `[target 2025-12-22] [status TODO]`
  - Deliverables: correctness plots (matplotlib/plotly script path recorded), perf profile (wall time, node expansions, pruning hits, tolerance-trigger counts) on HK2024; hardware baseline noted; artifacts stored under `packages/thesis/src/assets/figures/perf/...` (or shared store if large).
- Ablation + instrumentation results (e.g., pruning heuristics, ordering). Record what helps/hurts.  
  - `[target 2026-01-05] [status TODO] [depends previous bullet]`
  - Deliverables: ablation table + narrative; define varied knobs (ordering, pruning thresholds, heuristics), datasets/seeds, success metrics; recommendation on default heuristics; store results + script command used.

## Phase D – Experiments ramp
- Samplers + small test dataset + figure pipeline wired into thesis/docs-site. Configs checked in; figures visible.  
  - `[target 2026-01-12] [status TODO]`
  - Deliverables: test dataset (≤LFS threshold; otherwise git-lfs), configs in `packages/python_viterbo/data/configs/` with schema tests, figure assets in thesis path, snapshot tests for schema/figures; regenerate command recorded; define size cap for in-repo vs LFS; specify figure-generation command.
- Large dataset run (10^6-scale or chosen size) with schema regression guards; stored via git-lfs or shared store.  
  - `[target 2026-01-26] [status TODO] [risk runtime/cost]`
  - Deliverables: production dataset with schema checks; storage location documented (git-lfs vs `/workspaces/worktrees/shared/...`), rerun command recorded; size threshold policy stated (e.g., >50MB → LFS/shared); specify target sample size, budget/hardware, retention policy.

## Phase E – Thesis freeze window
- Code freeze for thesis; doc polish only.  
  - `[target 2026-02-15] [status TODO] [risk schedule drift]`
  - Define freeze branch/tag and allowed exceptions; checklist location (e.g., `docs/freeze-checklist.md`).
- Submission.  
  - `[target 2026-03-??] [status TODO]`
  - Deliverables: PDF + site RC; approval chain; sign-off criteria for RC; submission steps; target date to be fixed.

---

## Working notes / decisions
- Start with non-lagrangian-only algorithm to avoid numerical instability; near-lagrangian handling may come later (perturb-and-approx vs bespoke handling).
- Near-lagrangian support: decide later whether to perturb-and-approx or add bespoke handling; record ownership and phase when chosen so earlier artifacts stay valid.
- Keep Rust/Lean/Python/Thesis in sync; any change to one requires at least a note or matching tweak in the others.
- Tests: baseline polytopes (simplex, cube, crosspolytope, HK2024, etc.) must be codified once capacities/sys ratios are confirmed.
- Experiments must be scripted (config-driven) and reproducible; artifacts stored via git-lfs or shared store with commit provenance.
- Agentctl reliability is currently a risk (session discovery confusion, missing `final_message.txt`). Track via issues #6 and #7; avoid relying on `agentctl start` for critical tasks until fixed.
- Prefer `gh ... --body-file` (never `--body`) to avoid shell escaping problems when filing issues/PRs.

## Update workflow
- Weekly (Mondays): refresh statuses, slide dates if needed, append rationale for changes. `[owner Jörn]` Record rationale in this file under the relevant bullet.
- When adding a new phase item: include `[target] [status] [owner] [depends]` tags.
- Link to related GitHub issues when risks are mentioned (e.g., agentctl issues #6, #7).
