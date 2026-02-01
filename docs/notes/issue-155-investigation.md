# Issue #155 Investigation: Random Polytope Failures

**Investigation Date**: 2026-02-01
**Status**: Root causes identified, escalation needed

## Summary

Both the Tube and HK2017 algorithms fail on nearly all random 8-facet polytopes, while fixtures (cross-polytope, tesseract, etc.) work correctly.

## Symptoms

| Symptom | Observation |
|---------|-------------|
| Tube failures | 975/976 (99.9%) random polytopes fail with `NoClosedOrbits` |
| HK2017 failures | 100% fail with `NoFeasibleInteriorPoint` (primarily `negative_beta`) |
| Comparison test | Passes with 0 comparisons - functionally absent |

## Root Cause Analysis

### Primary Root Cause: Asymmetric Transition Graphs

Random H-rep polytopes create **sink facets** where the Reeb flow terminates:

**Cross-polytope (works):**
- 32 2-faces, 64 transitions
- Fully connected: 32/32 2-faces reachable from any start
- High symmetry ensures every facet appears equally as entry and exit

**Random polytope seed=0 (fails):**
- 14 2-faces, 25 transitions
- Nearly disconnected: only 1/14 2-faces reachable from 2-face 0
- **Facet 1 is a sink**: appears as exit in 4 2-faces, never as entry
- 2-faces 0-3 exit to facet 1 → 0 outgoing transitions → dead ends
- Facets 0, 6 don't appear in any 2-face → isolated

This creates a **nearly acyclic transition graph** where tubes cannot close.

### Why Random Polytopes Have Sink Facets

The random H-rep generator samples:
1. Normals uniformly from S³ (via Gaussian normalization)
2. Heights uniformly from [0.3, 3.0]

This produces valid bounded polytopes (~80% success rate), but the **combinatorial structure is unconstrained**:
- No guarantee of symmetric facet adjacency
- Some facets may dominate (many 2-faces exit to them)
- Other facets become sinks or don't participate at all

The cross-polytope's high symmetry (hyperoctahedral group) ensures balanced adjacency.

### HK2017 Failure Mode

The `negative_beta` rejections (107K out of 109K checked permutations) indicate that for random polytopes, the constrained optimization:

```
max Q(σ, β) subject to:
  Σ βᵢhᵢ = 1  (height)
  Σ βᵢnᵢ = 0  (closure in ℝ⁴)
  βᵢ ≥ 0     (positivity)
```

has no interior feasible points for most permutations. This is likely related to the same asymmetric geometry that causes sink facets - the normals and heights don't combine to give positive β solutions.

### Comparison Test Gap

`hk2017_comparison.rs:99-105` only prints a warning when `compared < 5`:

```rust
if compared < 5 {
    println!("WARNING: Only compared {} polytopes (target: 5)", compared);
}
// No assertion - test passes regardless
```

## Hypotheses Tested

| # | Hypothesis | Result | Evidence |
|---|-----------|--------|----------|
| 1 | Random polytopes are invalid | **FALSIFIED** | ~80% pass generator validation |
| 2 | Near-Lagrangian 2-faces cause issues | Partial | Random ω ∈ [0.001, 0.817] vs cross ω ∈ [0.5, 1.0] |
| 3 | Tolerance too strict | **FALSIFIED** | Tested 1e-10 to 1e-2, same failure |
| 4 | Transition graph disconnected | **CONFIRMED** | Random: 1/14 reachable; Cross: 32/32 |
| 5 | Sink facets prevent closure | **CONFIRMED** | Facet 1 has 4 incoming, 0 outgoing |

## Recommendations

### 1. Fix Comparison Test (Easy)

Add assertion in `hk2017_comparison.rs`:

```rust
assert!(compared >= 5, "Insufficient comparisons: only {} succeeded", compared);
```

Or use a retry-based approach with curated seeds known to work.

### 2. Improve Random H-rep Generator (Medium)

The current generator produces geometrically valid but algorithmically incompatible polytopes. Options:

a) **Filter by transition graph connectivity**: Reject polytopes where transition graph has unreachable 2-faces or no cycles

b) **Perturb fixtures**: Start from cross-polytope/24-cell and apply small random perturbations that preserve connectivity

c) **Constrained sampling**: Sample normals in a way that ensures balanced adjacency

### 3. Document Limitations (Easy)

Add documentation that random_hrep produces polytopes that may fail capacity algorithms due to transition graph structure.

## Files Modified During Investigation

- `tube/tests/detailed_diagnostic.rs` - Added diagnostic tests (should be removed or `#[ignore]`d before merge)

## Next Steps

1. **Escalate to Jörn**: The random polytope generator design is a thesis-level decision
2. **Quick fix**: Add assertion to comparison test to make it fail explicitly
3. **Research**: Is there a known class of polytopes guaranteed to have connected transition graphs?

## Related Issues

- #144: HK2017 vs Tube comparison test lacks effective cross-validation
- #155: Random polytope test failures
