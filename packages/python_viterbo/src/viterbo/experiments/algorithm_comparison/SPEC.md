# algorithm-comparison Experiment

**Status:** In Progress

## Research Question

How do the three EHZ capacity algorithms (HK2017, Billiard, Tube) compare in terms of:
1. Agreement on overlapping domains (do they give the same capacity?)
2. Success/failure domains (which polytopes work for which algorithm?)

## Method

### Polytope Selection

**Choices made without systematic evaluation:**
- Fixed test cases were chosen as "first idea accepted" - no comparison of alternatives
- Random polytopes added after user feedback

**Known literature values used for validation:**
| Polytope | Expected Capacity | Source |
|----------|------------------|--------|
| Tesseract [-1,1]^4 | 4.0 | HK2017 Example 4.6 |
| Pentagon × RotatedPentagon(90°) | 2cos(π/10)(1+cos(π/5)) ≈ 3.441 | HK-O 2024 counterexample |
| Cross-polytope | 1.0 | tube/src/fixtures.rs (empirically determined) |

**Polytope categories tested:**
1. Fixed Lagrangian products with known values (validation)
2. Random n-gon × m-gon products (coverage)

**TODO: Non-Lagrangian polytopes (for next agent):**
Fixtures exist in `rust_viterbo/tube/src/fixtures.rs`:
- `unit_cross_polytope()` — 16 facets, capacity 1.0
- `unit_24_cell()` — 24 facets
- `asymmetric_cross_polytope(seed)` — perturbed 16-facet
- `random_hrep(n_facets, min_omega, seed)` — random non-Lagrangian

These need to be exposed via FFI and added to stage_build.py.

**Not tested (potential gaps):**
- Systematic parameter sweeps
- Edge cases near algorithm boundaries

### Stages

1. **stage_build**: Generate test polytopes, run HK2017 + Billiard, store results
2. **stage_analyze**: (TODO) Compare capacities, compute statistics
3. **stage_plot**: (TODO) Visualize agreement/disagreement patterns

## Success Criteria

- Document which algorithm pairs agree/disagree
- Identify systematic discrepancies
- Validate against known literature values

## Expected Outputs

- data/algorithm-comparison/results.json
- assets/algorithm-comparison/comparison_table.png

## TODO for Next Agent

### 1. Add Non-Lagrangian Fixtures to FFI

Add to `rust_viterbo/ffi/src/lib.rs`:
```python
# Functions to expose:
unit_cross_polytope() -> (normals: list[list[float]], heights: list[float])
unit_24_cell() -> (normals: list[list[float]], heights: list[float])
asymmetric_cross_polytope(seed: int) -> (normals, heights)
random_hrep(n_facets: int, min_omega: float, seed: int) -> Option<(normals, heights)>
```

### 2. Update stage_build.py

- Add a `NonLagrangianRecord` dataclass (no vertices_q/p, has normals/heights instead)
- Generate non-Lagrangian polytopes using FFI fixtures
- Run HK2017 + Tube on them (Billiard will be N/A)
- Question: Is HK2017 fast enough for 16-facet cross-polytope? Test empirically.

### 3. Known Issues

- **triangle×triangle discrepancy:** Billiard=3.0, HK2017=1.5 (2× factor). Not debugged.
- **HK2017 vs Tube disjoint domains:** Earlier Rust exploration found 0 overlap in 1000 random 8-facet polytopes.

### 4. Questions to Resolve

- What is the expected capacity of the 24-cell? (Not documented in fixtures)
- Can HK2017 handle 16 facets in reasonable time with GraphPruning?

