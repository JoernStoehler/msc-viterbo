# algorithm_inventory Experiment

**Status:** Specified

## Research Question

What algorithms, fixtures, and validation tests exist in the Rust codebase, and do they pass?

This experiment produces the data for thesis sections 1-4 of `appendix-detailed-experiments`:
1. Algorithm Inventory
2. Polytope Test Fixtures
3. Correctness Validation
4. Capacity Comparison Matrix

## Method

### Stage 1: Build (`stage_build.py`)

**Goal:** Generate raw data by running algorithms and validation checks.

#### 1.1 Algorithm Inventory

Enumerate algorithms from hardcoded list (algorithms are stable):

| Algorithm | Variant | Source | Status |
|-----------|---------|--------|--------|
| HK2017 | naive | `hk2017/enumerate/naive.rs` | Implemented |
| HK2017 | graph-pruned | `hk2017/enumerate/graph.rs` | Implemented |
| Tube | — | `tube/algorithm.rs` | Implemented |
| Billiard | — | — | Absent (blocked) |

Output: `data/algorithm_inventory/algorithms.json`

#### 1.2 Fixture Inventory

Enumerate fixtures from hardcoded list matching `tube/src/fixtures.rs`:

**4D Fixtures:**
| Name | Facets | Lagrangian 2-faces | Tube-compatible |
|------|--------|-------------------|-----------------|
| unit_cross_polytope | 16 | No | Yes |
| unit_tesseract | 8 | Yes (all) | No |
| four_simplex | 5 | Yes | No |
| unit_24_cell | 24 | No | Yes |
| asymmetric_cross_polytope(seed) | 16 | No | Yes |
| scaled_cross_polytope(λ) | 16 | No | Yes |

**2D Primitives (for Lagrangian products):**
| Name | Vertices | Source |
|------|----------|--------|
| regular(n, r, θ) | n | `geom/src/polygon2d.rs` |
| square(s) | 4 | `geom/src/polygon2d.rs` |
| regular_pentagon() | 5 | `geom/src/polygon2d.rs` |

Output: `data/algorithm_inventory/fixtures.json`

#### 1.3 Capacity Matrix

For each (fixture, algorithm) pair where algorithm is applicable:
- Run capacity computation via FFI
- Record: capacity value, success/error, timing

Applicability rules:
- HK2017: Any polytope (but O(F!) complexity)
- Tube: Polytopes without Lagrangian 2-faces

Output: `data/algorithm_inventory/capacity_matrix.json`

#### 1.4 Validation Propositions

Test mathematical properties on each fixture:

| ID | Proposition | Implementation |
|----|-------------|----------------|
| P1 | Scaling: c(λK) = λ²c(K) | Compute c(2K), verify c(2K) = 4·c(K) |
| P2 | Mahler bound: c(K)·c(K°) ≤ 4 | Compute both, check product (K° requires dual computation) |
| P3 | Constraint satisfaction | Verify HK2017 output: β≥0, Σβᵢhᵢ=1, Σβᵢnᵢ=0 |
| P4 | Algorithm agreement | HK2017 = Tube on common domain (within 1% tolerance) |
| P5 | Orbit closure | Verify Tube output: ||p_first - p_last|| < ε |

For each (fixture, proposition) pair:
- Record: PASS/FAIL/SKIP/ERROR
- Record: numerical deviation (where applicable)
- Record: notes (skip reason, error message)

Output: `data/algorithm_inventory/validation_results.json`

### Stage 2: Tabulate (`stage_tabulate.py`)

**Goal:** Convert JSON data to LaTeX tables for thesis inclusion.

Read JSON files from stage_build, generate:
- `assets/algorithm_inventory/table-algorithms.tex`
- `assets/algorithm_inventory/table-fixtures.tex`
- `assets/algorithm_inventory/table-validation.tex`
- `assets/algorithm_inventory/table-capacity-matrix.tex`

Tables use standard LaTeX tabular environment with `\input{}` inclusion.

## Implementation Notes

### Enumeration Strategy: Hardcoded Lists

**Rationale:** Algorithms and fixtures are few and stable. Introspection (parsing Rust source or FFI reflection) adds complexity without proportional benefit. A hardcoded list is:
- Easy to maintain (single source of truth in Python)
- Easy to extend (add new entries as algorithms/fixtures are added)
- Readable and auditable

When Rust code changes, update the hardcoded list in `stage_build.py`.

### Validation Execution: FFI + Python Logic

**Rationale:** Capacity computation is expensive and already implemented in Rust. Validation logic (checking ratios, products, tolerances) is simple and natural in Python.

- Use FFI (`viterbo_ffi`) to call `hk2017_capacity()` and `tube_capacity()`
- Implement proposition checks in Python
- P3 and P5 require access to algorithm output details (β coefficients, orbit breakpoints), which may require FFI extensions if not already exposed

**FFI requirements:**
- `hk2017_capacity(normals, heights, strategy) -> Result with .capacity, .betas, .sigma`
- `tube_capacity(normals, heights) -> Result with .capacity, .breakpoints`

If FFI doesn't expose needed fields, fall back to subprocess `cargo test` with `--nocapture` parsing.

### Output Format

All data outputs are JSON (human-readable, easy to parse):
```json
// capacity_matrix.json
{
  "entries": [
    {
      "fixture": "unit_cross_polytope",
      "algorithm": "hk2017_naive",
      "capacity": 1.0,
      "status": "success",
      "time_ms": 42
    },
    ...
  ],
  "generated_at": "2026-01-30T12:00:00Z"
}
```

### Dual Polytope (P2)

Computing K° requires vertex enumeration and polar transformation. The `tube::preprocess` module already computes vertices; we may need to add a `compute_polar()` function or skip P2 if it requires significant new code.

**Decision:** Mark P2 as "deferred" if polar computation is not readily available. The experiment can be extended later.

## Success Criteria

1. **Rerunnable:** Running `stage_build.py` produces consistent JSON outputs
2. **Thesis-ready:** Running `stage_tabulate.py` produces LaTeX tables matching `appendix-experiments-spec.md` format
3. **Complete:** All (fixture, algorithm) pairs attempted; all propositions tested on all applicable fixtures
4. **Documented:** FINDINGS.md summarizes validation status with escalation procedures

## Expected Outputs

### Data Files
- `data/algorithm_inventory/algorithms.json`
- `data/algorithm_inventory/fixtures.json`
- `data/algorithm_inventory/capacity_matrix.json`
- `data/algorithm_inventory/validation_results.json`

### Thesis Assets
- `packages/latex_viterbo/assets/algorithm_inventory/table-algorithms.tex`
- `packages/latex_viterbo/assets/algorithm_inventory/table-fixtures.tex`
- `packages/latex_viterbo/assets/algorithm_inventory/table-validation.tex`
- `packages/latex_viterbo/assets/algorithm_inventory/table-capacity-matrix.tex`

### Documentation
- `FINDINGS.md` (in this directory)

## Dependencies

- `viterbo_ffi` Python package (FFI bindings to Rust)
- Rust workspace builds successfully (`scripts/test.sh` passes)

## Out of Scope

- Billiard algorithm (not implemented)
- Runtime benchmarks (separate experiment: `benchmark_hk2017`)
- Profiling (separate experiment: `runtime_performance_analysis`)
- Random polytope generation statistics (could be added as P6 if needed)
