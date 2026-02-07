# Archaeology of msc-viterbo

This branch is a curated, flat snapshot of the msc-viterbo repository (the predecessor to msc-math). It exposes content that was scattered across git history — deleted docs, reverted implementations, resolved bugs — so future agents can explore it with simple file search instead of `git log` archaeology.

**This branch is read-only reference material. Nothing here will be built or run.**

---

## How to use this branch

```bash
# Shallow clone just this branch
git clone --branch archaeology --depth 1 <repo-url>

# Then grep/glob for what you need
grep -r "capacity" recovered-docs/
grep -r "tesseract" recovered-code/tests/
```

---

## What's here

### `recovered-docs/` — 51 files, ~700K of recovered documentation

Deleted from HEAD during repo restructurings. Contains the most detailed algorithm specs, mathematical claims, correctness proofs, and bug findings from the project.

**Start here:**

| File | What it is |
|------|-----------|
| `mathematical-claims.md` | Single source of truth for all mathematical claims: capacity axioms, known values, algorithm-specific claims, geometric foundations, Viterbo conjecture status |
| `literature-capacities.md` | Ground truth capacity values from published literature with exact formulas and sources |
| `developer-spec-v2.md` | Master spec consolidating all three algorithms (Billiard, HK2017, Tube) with data structures and test categories |
| `test-propositions.md` | Mathematical propositions that unit tests should verify, with implication tables |

**Algorithm specs (one per algorithm):**

| File | Algorithm | Scope |
|------|-----------|-------|
| `spec-billiard.md` | Billiard | Minkowski billiard on Lagrangian products. Bounce bound theorem, T-length formula, edge enumeration |
| `spec-hk2017.md` | HK2017 | Quadratic programming on all polytopes. Q-function formula, constraint set M(K), permutation enumeration |
| `tube-SPEC.md` | Tube | Branch-and-bound for non-Lagrangian polytopes. Quaternion trivialization, tube data structure, pruning |
| `tube-geometry-spec.md` | Tube | Geometry details: 2-face trivialization, polygon intersection, flow maps |
| `tube-SPEC-proofs.md` | Tube | Proofs of tube algorithm claims |

**Thesis chapter drafts (markdown, pre-LaTeX):**

| File | Content |
|------|---------|
| `thesis-02-math.md` | Math background: symplectic geometry in R^4, convex bodies, Lagrangian 2-planes |
| `thesis-ehz-capacity.md` | EHZ capacity definition: Reeb orbits, action integral, generalized characteristics |
| `thesis-algo-oriented-edge-graph.md` | Tube algorithm as directed cycle search on non-Lagrangian 2-face graph |
| `thesis-algo-minkowski-billiard.md` | Billiard algorithm: reflection law, support functions, 2/3-bounce enumeration |
| `math-introduction-draft.md` | Mathematical introduction draft |

**Bug findings and dead ends:**

| File | What happened |
|------|--------------|
| `findings-orbit-validation.md` | Billiard returned invalid orbits: only validated q-displacement, not full 2k-segment structure. Pentagon returned 2.127 instead of 3.441. Fixed in b5d43c9. |
| `findings-trivialization-bug.md` | Trivialization formula tau_n(V) = (VJn, VKn) doesn't biject on 2-face tangent spaces. Invalidated round-trip and symplecticity claims. Resolved. |
| `billiard-correctness-proof.md` | Analysis: LP-based billiard is rigorous, but older heuristic implementation is NOT proven correct for all inputs |
| `complexity-audit.md` | Identified sources of complexity: uncited claims, magic numbers, O(n!) algorithms, coupling, test gaps |

**Other recovered docs:**

| File | Content |
|------|---------|
| `trivialization-derivation.md` | Corrected derivation of 2-face trivialization using quaternion matrices i, j, k from CH2021 |
| `open-questions.md` | Resolved questions: trivialization normal convention (use exit facet), transition matrix direction, action function derivation |
| `claims-audit-notes.md` | Audit of mathematical claims in the codebase |
| `impl-plan-hk2017.md` | HK2017 implementation plan |
| `billiard-SPEC.md`, `billiard-TEST_SPEC.md` | Billiard crate spec and test spec |
| `hk2017-SPEC.md` | HK2017 crate spec |
| `geom-SPEC.md` | Geometry crate spec |
| `optim-SPEC.md` | Optimization crate spec |
| `ffi-contract.md` | Rust-Python FFI contract |
| `root-SPEC.md` | Root project specification |
| `conv-math-code-correspondence.md` | Math-to-code naming conventions |
| `conv-rust-algorithms.md` | Rust algorithm conventions |
| `proto-math-*.md` (6 files) | Early mathematical definition drafts (capacity, constructions, polar, polytope, symplectic, volume) |
| `lit-*.md` (3 files) | Literature summaries: Haim-Kislev 2019, HK-O 2024, Rudolf 2022 |
| `algorithm-billiard-spec.md` | Earlier billiard algorithm spec |
| `algorithm-hk2019-spec.md` | HK2019 algorithm spec |
| `algorithm-spec.md` | General algorithm specification |

---

### `recovered-code/` — 35 files, ~19K lines of Rust

Deleted or reverted algorithm implementations and test suites recovered from git history.

**`algorithm-archive/`** — consolidated algorithm crate (from commit f613c166):

| File | Lines | What it is |
|------|-------|-----------|
| `billiard.rs` | 948 | Billiard algorithm: LagrangianFactors, BilliardTrajectory, Polygon2DSimple, edge enumeration |
| `hk2019.rs` | 809 | HK2019 algorithm — **MARKED BROKEN**: QP solver only checks 0D/1D faces, misses optima on 2D+ faces. Returns wrong values. |
| `tube.rs` | 1145 | Tube algorithm: Tube struct, flow maps, action functions, branch-and-bound |
| `billiard_lp.rs` | 1155 | LP-based billiard variant |

**`billiard-deleted/`** — earlier billiard implementation (from commit 46095acd):

| File | Lines | What it is |
|------|-------|-----------|
| `algorithm.rs` | 320 | Main billiard capacity entry point |
| `action.rs` | 105 | Action computation for billiard trajectories |
| `solve.rs` | 522 | Constrained optimization solver |
| `types.rs` | 334 | Type definitions for billiard algorithm |

**`tube-reverted/`** — reverted tube implementation (from commit 2b71e367):

| File | Lines | What it is |
|------|-------|-----------|
| `tube.rs` | 620 | Core tube algorithm with branch-and-bound |
| `geom.rs` | 345 | 2D geometry for trivialization |
| `polytope.rs` | 595 | Polytope data structures |
| `trivialization.rs` | 218 | Coordinate trivialization along 2-faces |

**`tests/`** — 23 test files with concrete numeric values:

| File | Lines | Key values |
|------|-------|-----------|
| `capacity_known_values.rs` | 1084 | tesseract=4.0, triangle product=1.5, pentagon (HK-O)=3.441, simplex=0.25 |
| `fixtures.rs` | 1706 | Polytope constructors, ground truth table, random generator seeds (57, 1729) |
| `tube_fixtures.rs` | 816 | Cross-polytope=1.0, tesseract=4.0, scaling fixtures |
| `tube_integration.rs` | 347 | c(cross)=1.0, c(2K)=4c(K), Mahler bound c(K)c(K^o)<=4 |
| `tube_hk2017_comparison.rs` | 213 | Cross-algorithm validation on random 8-facet polytopes (1% tolerance) |
| `billiard_comprehensive_comparison.rs` | 198 | Billiard vs HK2017 on square/rectangle/triangle/pentagon products |
| Other test files | ~8K | Algorithm agreement, scaling axiom, monotonicity, symplectomorphism invariance, orbit invariants |

---

### `crates/` — Rust workspace (on HEAD)

The final state of the Rust codebase. Most crates are stubs, but geom4d has real content.

| Crate | Status | Key content |
|-------|--------|------------|
| `geom2d` | Minimal | `area.rs` (signed area), `polygon.rs` (2D polygon type), `tolerances.rs` |
| `geom4d` | Partial | `hrep.rs` (H-representation polytope), `bounded.rs` (boundedness check via LP), `tolerances.rs` (EPS, EPS_HEIGHT, EPS_UNIT, MAX_COORD) |
| `hk2017` | Stub | Empty lib.rs |
| `billiard` | Stub | Empty lib.rs |
| `tube` | Stub | Empty lib.rs |
| `ffi` | Stub | Python FFI bridge (empty) |

---

### `thesis/` — LaTeX thesis (on HEAD)

Compiled thesis chapters with mathematical definitions, algorithm descriptions, and counterexample analysis.

| File | Content |
|------|---------|
| `chapters/intro.tex` | Introduction and thesis goals |
| `chapters/math.tex` | Math background: symplectic form, EHZ capacity, systolic ratio, Reeb dynamics, HK combinatorial formula |
| `chapters/algorithms.tex` | Three algorithms: HK2017 (combinatorial QP), CH2021/Tube (branch-and-bound), Billiard (LP on Lagrangian products) |
| `chapters/counterexample.tex` | HK-O pentagon counterexample: c=3.441, vol=5.655, sys=1.047 |
| `chapters/experiments.tex` | Cross-polytope c=1.0, Mahler saturation, scaling law verification |
| `chapters/conjectures.tex` | Placeholder for computational conjectures |
| `preamble.tex` | LaTeX packages and custom macros |

---

### `experiments/` — Python experiment pipeline (on HEAD)

| Experiment | Status | Key findings |
|-----------|--------|-------------|
| `algorithm_inventory` | Complete | HK2017 infeasible for >8 facets; Tube handles 16-24; Mahler bound saturated on tesseract/cross-polytope |
| `benchmark_hk2017` | Complete | time_ms = 5.51e-4 * perms^1.059 (R^2=0.9997); ~1 us/permutation; graph pruning gives 2-7x speedup |
| `runtime_performance_analysis` | Complete | Tube ~1.6 us/tube; 20% of runtime is malloc/free |
| `counterexample_hko` | Complete | Pentagon product sys=1.118 > 1 (violates Viterbo); orbit is 2-bounce T-billiard |
| `algorithm_comparison` | Partial | Triangle x Triangle discrepancy: Billiard=3.0 vs HK2017=1.5 (unresolved) |
| `polytope_database` | Partial | Polytope families: tesseract, simplex, cross-polytope, 24-cell, random |
| `polytope_visualization_4d` | Complete | 4D projection pipeline: radial -> stereographic -> Plotly |

---

### `docs/papers/` — Reference paper LaTeX sources

| Code | Paper | Topic |
|------|-------|-------|
| HK2017 | Haim-Kislev 2017 | EHZ capacity formula; simple orbit theorem |
| HK2024 | Haim-Kislev-Ostrover 2024 | Pentagon counterexample (sys > 1) |
| CH2021 | Chaidez-Hutchings 2021 | Tube algorithm, rotation numbers |
| Rudolf2022-billiard | Rudolf 2022 | Billiard characterization |
| Rudolf2022-worm | Rudolf 2022 | Viterbo as worm problem |
| Irie2019 | Irie 2019 | SH capacity = EHZ |
| Irie2010 | Irie 2010 | n+1 bounce billiards |
| AK2019 | Abbondandolo-Kang 2019 | Clarke dual action |
| BezdekBezdek2009 | Bezdek-Bezdek 2009 | Shortest billiard trajectories |

---

## Ground truth capacity values

Extracted from `recovered-docs/literature-capacities.md` and `recovered-code/tests/capacity_known_values.rs`:

| Polytope | Capacity | Exact formula | Source |
|----------|----------|--------------|--------|
| Unit ball B^4 | pi | pi | Classical |
| Tesseract [-1,1]^4 | 4.0 | 4 | HK2017 Example 4.6 |
| Cross-polytope (16-cell) | 1.0 | 1 | Empirical (tube), dual of tesseract |
| 24-cell | 2.0 | 2 | Empirical (tube) |
| Standard 4-simplex | 0.25 | 1/4 | Computed |
| Equilateral triangle x triangle | 1.5 | 3/2 | Computed, cross-validated |
| Pentagon x R(90)Pentagon (HK-O) | 3.441 | 2cos(pi/10)(1+cos(pi/5)) | HK-O 2024 Theorem 1.1 |
| Mahler: tesseract x cross | 4.0 x 1.0 = 4.0 | Saturates c(K)c(K^o) <= 4 | |
| Mahler: 24-cell (self-dual) | 2.0^2 = 4.0 | Saturates c(K)c(K^o) <= 4 | |

Systolic ratio for HK-O counterexample: sys = (sqrt(5)+3)/5 = 1.0472... > 1 (falsifies Viterbo).

**Note:** The `thesis/chapters/counterexample.tex` uses sys = c^2/(4*vol), while `recovered-docs` sometimes uses sys = c^2/(2*vol). Check the normalization convention before using values.

---

## Known bugs and dead ends

1. **HK2019 algorithm is BROKEN** (`recovered-code/algorithm-archive/hk2019.rs`). The QP solver only checks 0D and 1D faces of the feasible set. For indefinite quadratics, the maximum can lie on 2D+ faces — these are missed entirely. The algorithm returns plausible-looking but wrong values.

2. **Billiard orbit validation bug** (`recovered-docs/findings-orbit-validation.md`). A 2-bounce billiard has 4 affine segments (not 2); old code checked segments 2,4,6 but missed 1,3,5 (p-transitions at bounces). Pentagon x Pentagon returned 2.127 instead of 3.441. Fixed in commits b5d43c9, 05169c3.

3. **Trivialization formula bug** (`recovered-docs/findings-trivialization-bug.md`). The formula tau_n(V) = (<V,Jn>, <V,Kn>) doesn't provide a bijection on 2-face tangent spaces. This invalidated the round-trip property and transition matrix symplecticity claims. Resolved with corrected derivation in `recovered-docs/trivialization-derivation.md`.

4. **Triangle x Triangle discrepancy** (unresolved). Billiard algorithm returns 3.0, HK2017 returns 1.5 for equilateral triangle x triangle. Factor of 2 — not debugged at time of archival.

5. **HK2017 vs Tube domain overlap**. In 1000 random 8-facet polytopes, zero overlap between algorithm domains was found (all random polytopes had Lagrangian 2-faces, making them Tube-incompatible).

---

## What was stripped from this branch

- `.claude/` — agent configuration, skills, commands
- `.devcontainer/` — development environment setup
- `tasks/` — agent task management files
- `scripts/` — development tooling
- `docs/investigations/` — agent debugging reports (LSP issues, etc.)
- Python build/lint/test config files
- VS Code workspace file
- Example/template experiment directories
