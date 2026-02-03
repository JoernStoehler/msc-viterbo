# Appendix: Computational Experiments

**Status:** blocked
**Priority:** P2
**Blocked by:** Billiard algorithm not implemented

## Goal

Make the computational tools visible to thesis readers by documenting algorithms, tests, and empirical findings with data-driven tables and figures.

**Target file:** `thesis/chapters/appendix-detailed-experiments.tex`

## Chapter Structure

### 1. Algorithm Inventory

Overview of implemented algorithms and their variants.

| Algorithm | Variant | Applicability | Complexity | Implementation | Status |
|-----------|---------|---------------|------------|----------------|--------|
| HK2017 | naive | Any polytope | O(F!) | `hk2017/enumerate/naive.rs` | Implemented |
| HK2017 | graph-pruned | Sparse facet graphs | O(cycles) | `hk2017/enumerate/graph.rs` | Implemented |
| Tube | - | No Lagrangian 2-faces | Branch-and-bound | `tube/algorithm.rs` | Implemented |
| Billiard | - | Lagrangian products | TBD | `billiard/` | **Absent (blocked)** |

### 2. Polytope Test Fixtures

**2D Primitives (for Lagrangian products):**
| Name | Vertices | Description |
|------|----------|-------------|
| unit_square | 4 | [-1,1]^2 |
| unit_triangle | 3 | Regular, centered |
| regular_n_gon(n) | n | Regular n-gon |

**4D Fixtures:**
| Name | Facets | Vertices | Lagrangian 2-faces | Known capacity | Source |
|------|--------|----------|-------------------|----------------|--------|
| cross_polytope | 16 | 8 | No | 1.0 | `tube/fixtures.rs` |
| tesseract | 8 | 16 | Yes (all) | 4.0 | `tube/fixtures.rs` |
| 4_simplex | 5 | 5 | Yes | ? | `tube/fixtures.rs` |
| 24_cell | 24 | 24 | No | ? | `tube/fixtures.rs` |
| asymmetric_cross(seed) | 16 | 8 | No | ~1.0 | `tube/fixtures.rs` |
| random_hrep(F, omega_min, seed) | F | varies | filtered | varies | `tube/fixtures.rs` |

### 3. Correctness Validation

Mathematical propositions tested, with pass/fail tables.

| ID | Proposition | Quantifier |
|----|-------------|------------|
| P1 | Scaling: c(lambda*K) = lambda^2 * c(K) | forall K, forall lambda>0 |
| P2 | Mahler bound: c(K)*c(K^o) <= 4 | forall K symmetric |
| P3 | Constraint satisfaction: beta>=0, sum(beta_i*h_i)=1, sum(beta_i*n_i)=0 | forall HK2017 output |
| P4 | Algorithm agreement: HK2017 = Tube (on common domain) | forall K without Lagrangian 2-faces |
| P5 | Orbit closure: final point ~= initial | forall Tube output |

### 4. Capacity Comparison Matrix

| Polytope | HK2017 (naive) | HK2017 (graph) | Tube | Notes |
|----------|----------------|----------------|------|-------|
| cross_polytope | 1.0 | 1.0 | 1.0 | Agreement |
| tesseract | 4.0 | 4.0 | N/A | Lagrangian 2-faces |

### 5. Runtime Benchmarks

Empirical runtime analysis with prediction heuristic.

### 6. Profiling Hotspots

Where does time go for relevant workloads?

## Data Artifacts

All experiment outputs go to: `experiments/appendix-experiments/`

| Artifact | Format | Producer |
|----------|--------|----------|
| `exp-validation-results.json` | JSON | Rust binary or Python script |
| `exp-capacity-matrix.json` | JSON | Rust binary or Python script |
| `exp-benchmark-results.json` | JSON | Criterion + post-processing |
| `exp-profiling-summary.md` | Markdown | Manual from flamegraph |
| `flamegraph-*.svg` | SVG | cargo-flamegraph |

## Dependencies

- Existing fixtures in `tube/src/fixtures.rs`
- No dependency on billiard (stub) - add later when implemented

## Out of Scope

- Billiard algorithm (not implemented)
- Lagrangian products of arbitrary polygons
- ML-based capacity prediction (separate experiment track)
- Formal proofs of algorithm correctness (thesis math chapter)
