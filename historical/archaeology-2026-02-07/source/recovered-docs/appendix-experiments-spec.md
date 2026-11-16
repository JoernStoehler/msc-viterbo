# Appendix: Computational Experiments - Specification

**Target file:** `packages/latex_viterbo/chapters/appendix-detailed-experiments.tex`

**Purpose:** Make the computational tools visible to thesis readers by documenting algorithms, tests, and empirical findings with data-driven tables and figures.

## Chapter Structure

### 1. Algorithm Inventory

**Content:** Overview of implemented algorithms and their variants.

| Algorithm | Variant | Applicability | Complexity | Implementation | Status |
|-----------|---------|---------------|------------|----------------|--------|
| HK2017 | naive | Any polytope | O(F!) | `hk2017/enumerate/naive.rs` | Implemented |
| HK2017 | graph-pruned | Sparse facet graphs | O(cycles) | `hk2017/enumerate/graph.rs` | Implemented |
| Tube | — | No Lagrangian 2-faces | Branch-and-bound | `tube/algorithm.rs` | Implemented |
| Billiard | — | Lagrangian products | TBD | `billiard/` | Absent (blocked) |

**Data needed:** None (code inspection only)

### 2. Polytope Test Fixtures

**Content:** Table of polytopes used in experiments.

**2D Primitives (for Lagrangian products):**
| Name | Vertices | Description |
|------|----------|-------------|
| unit_square | 4 | [-1,1]² |
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
| random_hrep(F, ω_min, seed) | F | varies | filtered | varies | `tube/fixtures.rs` |

**Data needed:** None (code inspection only)

### 3. Correctness Validation

**Content:** Mathematical propositions tested, with pass/fail tables.

**Propositions:**

| ID | Proposition | Quantifier | |
|----|-------------|------------|---|
| P1 | Scaling: c(λK) = λ²c(K) | ∀K, ∀λ>0 | |
| P2 | Mahler bound: c(K)·c(K°) ≤ 4 | ∀K symmetric | |
| P3 | Constraint satisfaction: β≥0, Σβᵢhᵢ=1, Σβᵢnᵢ=0 | ∀ HK2017 output | |
| P4 | Algorithm agreement: HK2017 = Tube (on common domain) | ∀K without Lagrangian 2-faces | |
| P5 | Orbit closure: final point ≈ initial | ∀ Tube output | |

**Per-proposition table:**
| Polytope | Result | Numerical error | Notes |
|----------|--------|-----------------|-------|
| cross_polytope | PASS | 1e-12 | |
| ... | | | |

**Data needed:** `exp-validation-results.json`
- Run each proposition on each applicable polytope
- Record: pass/fail/error, numerical deviation, timing

### 4. Capacity Comparison Matrix

**Content:** Table of capacity values across algorithms and polytopes.

| Polytope | HK2017 (naive) | HK2017 (graph) | Tube | Notes |
|----------|----------------|----------------|------|-------|
| cross_polytope | 1.0 | 1.0 | 1.0 | Agreement |
| tesseract | 4.0 | 4.0 | N/A | Lagrangian 2-faces |
| ... | | | | |

**Data needed:** `exp-capacity-matrix.json`
- For each (polytope, algorithm) pair: capacity value or error
- Include timing for context

### 5. Runtime Benchmarks

**Content:** Empirical runtime analysis with prediction heuristic.

**Raw data table:**
| Polytope | Facets | Vertices | Algorithm | Time (μs) | Nodes explored |
|----------|--------|----------|-----------|-----------|----------------|

**Analysis:**
1. Correlation of runtime with facet count, vertex count, other features
2. Hypothesis formation and testing (e.g., "facet count dominates")
3. Final heuristic: natural language + empirical formula
4. Prediction error on held-out set

**Data needed:** `exp-benchmark-results.json`
- Criterion benchmark output
- Random polytopes with varying facet counts (8, 10, 12, 14, 16)
- Multiple seeds per facet count for statistics

### 6. Profiling Hotspots

**Content:** Where does time go for relevant workloads?

**Workload definition:**
- "Relevant" = polytopes similar to what dataset experiments will use
- Random polytopes with F ∈ [8, 16], filtered for no Lagrangian 2-faces
- Random Lagrangian products of regular polygons (when available)

**Output:**
- Flamegraph (as figure)
- Top 5 hotspots with % time and interpretation
- Optimization opportunities (if any)

**Data needed:** `exp-profiling-summary.md` + flamegraph images

## Data Artifacts

All experiment outputs go to: `packages/python_viterbo/src/viterbo/experiments/appendix-experiments/`

| Artifact | Format | Producer |
|----------|--------|----------|
| `exp-validation-results.json` | JSON | Rust binary or Python script |
| `exp-capacity-matrix.json` | JSON | Rust binary or Python script |
| `exp-benchmark-results.json` | JSON | Criterion + post-processing |
| `exp-profiling-summary.md` | Markdown | Manual from flamegraph |
| `flamegraph-*.svg` | SVG | cargo-flamegraph |

## Dependencies

- #33: Benchmarks/profiling harness (provides criterion setup)
- Existing fixtures in `tube/src/fixtures.rs`
- No dependency on billiard (stub) - add later when implemented
- No dependency on #99 (geom library) - use existing fixtures

## Out of Scope

- Billiard algorithm (not implemented)
- Lagrangian products of arbitrary polygons (requires #99)
- ML-based capacity prediction (separate experiment track)
- Formal proofs of algorithm correctness (thesis math chapter)
