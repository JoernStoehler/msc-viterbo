# algorithm_inventory Findings

**Status:** Complete

## Summary

This experiment inventories the algorithms and test fixtures in the Rust codebase, computes capacity values for all applicable (fixture, algorithm) pairs, and validates mathematical properties.

## Key Results

### Capacity Values

| Fixture | Capacity | Algorithm Used |
|---------|----------|----------------|
| unit_cross_polytope | 1.0 | Tube |
| unit_tesseract | 4.0 | HK2017 |
| four_simplex | 0.4167 | HK2017 |
| unit_24_cell | 2.0 | Tube |

### Algorithm Applicability

- **HK2017**: Works on any polytope but has O(F!) complexity. Tractable only for F ≤ 8 facets.
- **Tube**: Works only on polytopes without Lagrangian 2-faces. Much faster than HK2017 on applicable polytopes.

### Validation Summary

| Proposition | Pass | Fail | Skip | N/A |
|-------------|------|------|------|-----|
| P1: Scaling | 2 | 0 | 0 | 0 |
| P2: Mahler bound | 2 | 0 | 0 | 0 |
| P3: Constraints | 2 | 0 | 2 | 0 |
| P4: Agreement | 0 | 0 | 2 | 2 |
| P5: Orbit closure | 0 | 0 | 2 | 2 |

**Total: 6 pass, 0 fail, 6 skip, 4 n/a**

## Observations

### 1. HK2017 Complexity Limits

The HK2017 algorithm (both naive and graph-pruned variants) is infeasible for polytopes with more than 8 facets:
- Cross-polytope (16 facets): Skipped
- 24-cell (24 facets): Skipped

Even the graph-pruned variant causes memory exhaustion on 16-facet polytopes. This is a fundamental limitation of the combinatorial approach.

### 2. Tube Algorithm Efficiency

The Tube algorithm is much more efficient on applicable polytopes:
- Cross-polytope: 1.2s (vs infeasible for HK2017)
- 24-cell: 249ms (vs infeasible for HK2017)

### 3. Mahler Bound Saturation

The tesseract × cross-polytope dual pair exactly saturates the Mahler bound:
- c(tesseract) = 4.0
- c(cross-polytope) = 1.0
- Product = 4.0 (exactly at the bound)

The 24-cell (self-dual) also saturates the bound:
- c(24-cell) = 2.0
- c² = 4.0 (exactly at the bound)

This suggests these polytopes may be extremal for the Mahler inequality in 4D.

## Escalation Procedures

1. **HK2017 on large polytopes**: If HK2017 results are needed for polytopes with > 8 facets, consider:
   - Implementing more aggressive pruning
   - Using parallel computation
   - Accepting Tube-only results for non-Lagrangian polytopes

2. **Rerun triggers**: If upstream Rust code changes capacity computations, rerun this experiment and compare results.

## Changelog

- 2026-01-30: Initial findings from algorithm_inventory experiment
