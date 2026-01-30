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

| ID | Proposition | Implementation | FFI Support |
|----|-------------|----------------|-------------|
| P1 | Scaling: c(λK) = λ²c(K) | Compute c(2K), verify c(2K) = 4·c(K) | ✓ capacity exposed |
| P2 | Mahler bound: c(K)·c(K°) ≤ 4 | Test on known dual pairs only | ✓ (limited) |
| P3 | Constraint satisfaction | Verify HK2017 output: β≥0, Σβᵢhᵢ=1, Σβᵢnᵢ=0 | ✓ optimal_beta exposed |
| P4 | Algorithm agreement | HK2017 = Tube on common domain (within 1% tolerance) | ✓ capacity exposed |
| P5 | Orbit closure | Verify Tube output: ||p_first - p_last|| < ε | ✗ breakpoints not exposed |

**P2 Implementation (Known Dual Pairs):**
General polar computation requires 4D convex hull (V-rep → H-rep), which is not implemented.
Instead, test P2 on known dual pairs:
- tesseract ↔ cross-polytope: c(tess)=4.0 (hardcoded), c(cross) computed → product = 4
- 24-cell is self-dual: c(24)·c(24) ≤ 4

**P5 Implementation (Orbit Closure):**
`TubeResult` in FFI exposes only `.capacity`, `.tubes_explored`, `.tubes_pruned`.
Orbit breakpoints are not exposed. Options:
1. Extend FFI to expose `optimal_orbit.breakpoints` (requires Rust change)
2. Run `cargo test tube::tests::orbit_invariants --nocapture` and check pass/fail
3. Skip P5 for now, note as "covered by Rust unit tests"

**Recommendation:** Use option (3) — note P5 as covered by existing Rust tests in `orbit_invariants.rs`.
The experiment documents that the validation exists; reimplementing it in Python adds no value.

For each (fixture, proposition) pair:
- Record: PASS/FAIL/SKIP/N/A
- Record: numerical deviation (where applicable)
- Record: notes (skip reason, test reference)

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

**Current FFI bindings** (from `ffi/src/lib.rs`):

```python
# HK2017
result = rust_viterbo_ffi.hk2017_capacity_hrep(normals, heights, use_graph_pruning=False)
result.capacity            # float
result.q_max               # float
result.optimal_permutation # list[int] - facet indices in optimal order
result.optimal_beta        # list[float] - β values at optimum ✓ (for P3)
result.permutations_evaluated
result.permutations_rejected

# Tube
result = rust_viterbo_ffi.tube_capacity_hrep(normals, heights)
result.capacity       # float
result.tubes_explored # int
result.tubes_pruned   # int
# NOTE: breakpoints NOT exposed (P5 cannot be validated via FFI)

# Utilities
rust_viterbo_ffi.volume_hrep(normals, heights)  # float
rust_viterbo_ffi.systolic_ratio(capacity, volume)  # float
```

**Proposition feasibility:**
- P1, P4: ✓ Use `.capacity` from both algorithms
- P2: ✓ Use known dual pairs (tesseract/cross, self-dual 24-cell)
- P3: ✓ Use `.optimal_beta` and `.optimal_permutation` from HK2017
- P5: ✗ Breakpoints not exposed; defer to Rust unit tests

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

**Investigation result:** General polar computation requires 4D convex hull (converting V-rep of K° to H-rep). The codebase has:
- `tube::preprocess::enumerate_vertices_4d()` — computes vertices from H-rep
- Formula K° = conv{n_i/h_i} gives V-rep of polar from H-rep
- But no H-rep from V-rep conversion (4D convex hull not implemented)

**Decision:** Test P2 only on known dual pairs where both capacities are available:
1. **tesseract ↔ cross-polytope**: c(tess)=4.0 (via HK2017), c(cross)≈1.0 (via Tube) → product ≈ 4
2. **24-cell (self-dual)**: c(24)² ≤ 4

This validates the Mahler bound on available fixtures without requiring new geometry code.

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
