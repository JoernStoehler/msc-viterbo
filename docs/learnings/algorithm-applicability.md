# Algorithm Applicability Learnings

**Source:** `packages/python_viterbo/src/viterbo/experiments/algorithm_inventory/FINDINGS.md`

## Algorithm Summary

| Algorithm | Applicability | Complexity | Practical Limit |
|-----------|--------------|------------|-----------------|
| HK2017 (naive) | Any polytope | O(F!) | F <= 8 |
| HK2017 (graph-pruned) | Any polytope | O(cycles) | F <= 10 |
| Tube | Non-Lagrangian only | O(tubes) | F = 16+ |

## Decision Tree

```
Is the polytope non-Lagrangian (no Lagrangian 2-faces)?
  YES -> Use Tube algorithm (fast, handles large F)
  NO  -> Use HK2017:
           F <= 8  -> Either variant works
           F <= 10 -> GraphPruned recommended
           F > 10  -> Infeasible (memory exhaustion)
```

## Reference Capacity Values

| Polytope | Facets | Capacity | Algorithm |
|----------|--------|----------|-----------|
| 4-simplex | 5 | 0.4167 | HK2017 |
| Tesseract | 8 | 4.0 | HK2017 |
| Cross-polytope | 16 | 1.0 | Tube |
| 24-cell | 24 | 2.0 | Tube |

## Mahler Bound Saturation

The Mahler inequality states: `c(K) * c(K^polar) >= 4`.

### Saturating pairs found:

1. **Tesseract x Cross-polytope** (polar duals):
   - c(tesseract) = 4.0
   - c(cross-polytope) = 1.0
   - Product = 4.0 (exact saturation)

2. **24-cell** (self-dual):
   - c(24-cell) = 2.0
   - c^2 = 4.0 (exact saturation)

### Implications

These polytopes may be **extremal** for the Mahler inequality in 4D. This is potentially significant for understanding Viterbo's conjecture boundary cases.

## HK2017 Limitations

Memory exhaustion occurs on large polytopes:
- Cross-polytope (16 facets): Skipped (infeasible)
- 24-cell (24 facets): Skipped (infeasible)

Even graph-pruned variant cannot help here - the combinatorial explosion is fundamental.

## Tube Algorithm Performance

When applicable, Tube is dramatically faster:

| Polytope | Tube Time | HK2017 Status |
|----------|-----------|---------------|
| Cross-polytope | 1.2s | Infeasible |
| 24-cell | 249ms | Infeasible |

## Validation Properties

Tested mathematical properties:

| Property | Description | Coverage |
|----------|-------------|----------|
| P1: Scaling | c(lambda*K) = lambda^2 * c(K) | Pass |
| P2: Mahler | c(K) * c(K^polar) >= 4 | Pass |
| P3: Constraints | beta >= 0, sum(beta*h) = 1, sum(beta*n) = 0 | Pass |
| P4: Agreement | HK2017 = Tube when both apply | Limited |
| P5: Orbit closure | Boundary orbit is closed | Limited |

P4 and P5 have limited coverage because few polytopes are both non-Lagrangian (Tube) and small enough (HK2017).

## Escalation Triggers

1. **Need HK2017 on F > 8**: Consider parallel computation or accept Tube-only
2. **Capacity values change**: Rerun algorithm_inventory and compare
3. **New polytope fails validation**: Check Lagrangian 2-face detection
