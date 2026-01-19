# HK2019 Algorithm Specification

Implementation guide for the Haim-Kislev (2019) quadratic programming algorithm.

**Status:** Implemented and tested.

## 1. Goal

Compute the EHZ capacity using the formula from Haim-Kislev (2019):

```
c_EHZ(K) = (1/2) * [max_{σ,β} Q(σ,β)]^{-1}
```

where:
- σ is a permutation of facet indices
- β are positive weights satisfying linear constraints
- Q(σ,β) is a quadratic form involving symplectic pairings

## 2. Mathematical Formula

For a polytope with facets having normals {n₁, ..., nₖ} and heights {h₁, ..., hₖ}:

```
Q(σ,β) = Σ_{j<i} β_{σ(i)} β_{σ(j)} ω(n_{σ(i)}, n_{σ(j)})
```

subject to:
- Σᵢ βᵢ hᵢ = 1  (normalization)
- Σᵢ βᵢ nᵢ = 0  (closure constraint)

## 3. Algorithm Steps

1. **Generate all permutations** of facet indices {0, 1, ..., F-1}
2. **For each permutation σ:**
   - Solve the constrained QP: maximize Q(σ,β) subject to linear constraints
   - Track the maximum Q value found
3. **Return capacity** = 0.5 / Q_max

### 3.1 QP Solver

The inner QP is solved via gradient projection:
- Initialize β uniformly
- Project onto constraint manifold
- Iterate gradient ascent with projection
- Use multiple restarts for robustness

## 4. Complexity

- **Permutations:** O(F!) where F is the number of facets
- **Per-permutation:** O(F³) for the QP solve
- **Total:** O(F! × F³)

### 4.1 Practical Limits

Based on profiling (release build, single-threaded):

| Facets | Permutations | Time (s) | µs/perm |
|--------|--------------|----------|---------|
| 5      | 120          | 0.02     | 186     |
| 6      | 720          | 0.4      | 541     |
| 7      | 5,040        | 4.3      | 860     |
| 8      | 40,320       | 37       | 924     |
| 9      | 362,880      | timeout  | ~1000   |
| 10     | 3,628,800    | rejected | -       |

**Recommendation:** Use only for polytopes with **≤8 facets**.

The code accepts up to 10 facets but 9+ will timeout at 60s.

To reproduce these benchmarks:
```bash
cd packages/python_viterbo
uv run maturin develop --release --manifest-path ../rust_viterbo/ffi/Cargo.toml
uv run python ../rust_viterbo/docs/hk2019-benchmark.py
```

## 5. Implementation

```rust
// Main entry point
pub fn compute_hk2019_capacity(hrep: PolytopeHRep) -> Result<CapacityResult, AlgorithmError>;

// With custom timeout
pub fn compute_hk2019_capacity_with_timeout(
    hrep: PolytopeHRep,
    timeout: Duration,
) -> Result<CapacityResult, AlgorithmError>;
```

### 5.1 Parameters

- `MAX_FACETS_HK2019 = 10`: Reject polytopes with >10 facets
- `DEFAULT_TIMEOUT_SECS = 60`: Default timeout in seconds

### 5.2 Error Handling

- `ValidationError`: Invalid input or too many facets
- `NoValidOrbits`: QP solver failed to converge for all permutations

## 6. References

- Haim-Kislev (2019): "On the Ekeland-Hofer-Zehnder capacity of difference bodies"
- CH2021 Theorem 1.4: Rotation bound restricts valid permutations (not yet implemented)

## 7. Future Improvements

1. **Rotation bound pruning:** Skip permutations where cumulative rotation exceeds limit
2. **Parallel permutation search:** Use rayon for embarrassingly parallel speedup
3. **Better QP solver:** Replace gradient projection with a proper QP library
