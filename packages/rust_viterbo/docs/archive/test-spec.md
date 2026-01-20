# Test Specification

This document specifies concrete test cases for validating the tube-based capacity algorithm.
Tests are organized by level: unit → integration → regression → property.

**Goal:** Prevent shipping a numerically plausible but mathematically wrong implementation.

## 1. Unit Tests (Rust, fast, deterministic)

### 1.1 Linear Algebra Conventions

**Already implemented:**
- `j_squared_is_minus_identity` - J² = -I
- `omega_is_antisymmetric` - ω(x,y) = -ω(y,x)
- `omega_matches_coordinate_formula` - ω(x,y) = q·p' - p·q'
- Quaternion relations (9 tests) - i²=j²=k²=-I, ij=k, etc.

**To add:**

| Test | Input | Expected | Purpose |
|------|-------|----------|---------|
| `omega_standard_basis` | ω(e₁,e₃), ω(e₂,e₄) | 1.0, 1.0 | Verify sign convention |
| `omega_standard_basis_neg` | ω(e₃,e₁), ω(e₄,e₂) | -1.0, -1.0 | Antisymmetry on basis |
| `omega_lagrangian_pairs` | ω(e₁,e₂), ω(e₃,e₄) | 0.0, 0.0 | q-q and p-p pairs are Lagrangian |
| `reeb_velocity_formula` | v = (2/h)Jn for unit n | ‖v‖ = 2/h, ⟨v,n⟩ = 0 | Reeb velocity is tangent to facet |

### 1.2 Flow Direction

| Test | Setup | Expected | Purpose |
|------|-------|----------|---------|
| `flow_direction_positive_omega` | n₁=(1,0,0,0), n₂=(0,0,1,0) | ω(n₁,n₂)=1 → flow I→J | Verify flow direction logic |
| `flow_direction_negative_omega` | n₁=(0,0,1,0), n₂=(1,0,0,0) | ω(n₁,n₂)=-1 → flow J→I | Opposite direction |
| `flow_direction_lagrangian` | n₁=(1,0,0,0), n₂=(0,1,0,0) | ω(n₁,n₂)=0 → Lagrangian | No flow direction |

### 1.3 Rotation Computation

| Test | Input normals | Expected ρ | Purpose |
|------|---------------|------------|---------|
| `rotation_orthogonal_normals` | n₁=(1,0,0,0), n₂=(0,0,1,0) | 0.25 (quarter turn) | Standard case |
| `rotation_45_degree` | n₁=(1,0,0,0), n₂=(1/√2,0,1/√2,0) | ~0.125 | Intermediate angle |
| `rotation_near_parallel` | n₁, n₂ nearly parallel | ρ → 0 | Edge case |
| `rotation_bounds` | Any valid pair | ρ ∈ (0, 0.5) | Always positive elliptic |

### 1.4 Affine Map Operations

| Test | Operation | Expected | Purpose |
|------|-----------|----------|---------|
| `affine_identity_compose` | id ∘ φ = φ | Equal | Identity is neutral |
| `affine_compose_associative` | (φ ∘ ψ) ∘ θ = φ ∘ (ψ ∘ θ) | Equal | Associativity |
| `affine_apply_point` | φ(p) = Ap + b | Correct result | Basic application |
| `affine_func_compose` | (f ∘ φ)(p) = f(φ(p)) | Equal | Function composition |

### 1.5 Polygon Operations

| Test | Operation | Expected | Purpose |
|------|-----------|----------|---------|
| `polygon_triangle_intersection` | Two overlapping triangles | Correct intersection polygon | Basic case |
| `polygon_disjoint` | Non-overlapping polygons | Empty | Emptiness detection |
| `polygon_contained` | P ⊂ Q | P ∩ Q = P | Containment |
| `polygon_affine_image` | φ(triangle) | Transformed vertices | Affine transform |
| `polygon_fixed_point_inside` | φ with fixed point in P | Find the fixed point | Closure solving |
| `polygon_fixed_point_outside` | φ with fixed point outside P | Empty result | No valid orbit |
| `polygon_no_fixed_point` | φ = id + translation | Empty result | No fixed point exists |

## 2. Integration Tests (Rust, tube algorithm correctness)

### 2.1 Witness Verification

For any returned witness orbit, verify:

| Check | Condition | Tolerance |
|-------|-----------|-----------|
| Breakpoints on boundary | ⟨nᵢ, p⟩ = hᵢ for active facet | 1e-10 |
| Breakpoints feasible | ⟨nⱼ, p⟩ ≤ hⱼ for all j | 1e-10 |
| Segment in facet | All points on segment satisfy active constraint | 1e-10 |
| Segment direction | direction ∝ Jnᵢ (Reeb velocity) | 1e-10 (angle) |
| Action consistency | sum(segment_times) = reported action | 1e-12 |
| Orbit closes | first breakpoint = last breakpoint | 1e-10 |

### 2.2 Determinism

| Test | Condition | Expected |
|------|-----------|----------|
| `deterministic_non_lagrangian` | Same non-Lagrangian input | Identical output |
| `deterministic_with_seed` | Same Lagrangian input + same seed | Identical output |
| `different_seeds_vary` | Same Lagrangian input + different seeds | May differ slightly |

### 2.3 Facet Reordering Invariance

| Test | Transformation | Expected |
|------|----------------|----------|
| `reorder_facets` | Permute facet order in H-rep | Same capacity (within 1e-10) |
| `reorder_vertices` | Permute vertex order in V-rep (if used) | Same capacity |

## 3. Regression Tests (Known Polytopes)

### 3.1 4D Unit Ball Approximation

The 4D ball B⁴(1) has c_EHZ = π. Approximate with regular polytopes:

| Polytope | Facets | Expected capacity | Tolerance | Notes |
|----------|--------|-------------------|-----------|-------|
| 4-simplex | 5 | < π | 20% | Very coarse |
| Tesseract [-1,1]⁴ | 8 | Compute exactly | 1e-6 | Axis-aligned, Lagrangian |
| 16-cell (cross-polytope) | 16 | Compute exactly | 1e-6 | Dual of tesseract |
| 24-cell | 24 | Closer to π | 10% | Self-dual |
| 120-cell | 120 | ≈ π | 5% | Good approximation |

### 3.2 Product Polytopes

For P × Q ⊂ ℝ² × ℝ²:

| Polytope | Formula | Expected | Notes |
|----------|---------|----------|-------|
| Square × Square | [0,a]² × [0,b]² | min(a²,b²)·π/2 | Cylinder-like |
| Triangle × Triangle | Δ × Δ | Depends on triangles | |

### 3.3 HK&O Counterexample

**Primary regression target.**

| Property | Value | Source |
|----------|-------|--------|
| Polytope | See `counterexample_hko/` data | HK&O 2024 |
| Expected capacity | Known closed-form | Paper |
| Systolic ratio | > 1 (counterexample!) | Paper |
| Tolerance | 1e-4 (calibrate after first run) | TBD |

Test must:
1. Load polytope from `packages/python_viterbo/data/counterexamples/hk-o-2024/`
2. Run capacity algorithm via FFI
3. Compare to known value
4. Record perturbation metadata (seed, epsilon)

### 3.4 Scaling Sanity Check

For each regression polytope:

| Test | Transform | Expected |
|------|-----------|----------|
| `scale_by_2` | K → 2K (heights × 2) | c(2K) = 4·c(K) |
| `scale_by_half` | K → K/2 (heights × 0.5) | c(K/2) = c(K)/4 |
| `scale_by_sqrt2` | K → √2·K | c(√2·K) = 2·c(K) |

## 4. Property Tests (proptest/quickcheck)

### 4.1 Scaling (2-homogeneity)

```rust
proptest! {
    fn capacity_scales_quadratically(
        polytope in valid_polytope_strategy(),
        scale in 0.1f64..10.0,
    ) {
        let scaled = scale_polytope(&polytope, scale);
        let c_original = compute_capacity(&polytope);
        let c_scaled = compute_capacity(&scaled);

        prop_assert!((c_scaled - scale * scale * c_original).abs() < tolerance);
    }
}
```

### 4.2 Symplectic Invariance

Test with block rotations in (q₁,p₁) and (q₂,p₂) planes:

```rust
proptest! {
    fn capacity_invariant_under_symplectic(
        polytope in valid_polytope_strategy(),
        theta1 in 0.0f64..TAU,
        theta2 in 0.0f64..TAU,
    ) {
        let rotated = apply_block_rotation(&polytope, theta1, theta2);
        let c_original = compute_capacity(&polytope);
        let c_rotated = compute_capacity(&rotated);

        prop_assert!((c_original - c_rotated).abs() < tolerance);
    }
}
```

### 4.3 Monotonicity

```rust
proptest! {
    fn capacity_monotonic(
        polytope in valid_polytope_strategy(),
        expansion in 1.01f64..2.0,
    ) {
        let expanded = expand_heights(&polytope, expansion);
        let c_original = compute_capacity(&polytope);
        let c_expanded = compute_capacity(&expanded);

        // K ⊂ expanded(K) implies c(K) ≤ c(expanded(K))
        prop_assert!(c_original <= c_expanded + tolerance);
    }
}
```

### 4.4 Witness Validity

```rust
proptest! {
    fn witness_is_valid(polytope in valid_polytope_strategy()) {
        let result = compute_capacity(&polytope);
        verify_witness(&result.witness, &polytope)?;
    }
}
```

## 5. FFI Tests (Python)

### 5.1 Input Validation (Negative Tests)

| Test | Invalid Input | Expected Error |
|------|---------------|----------------|
| `mismatched_lengths` | len(normals) ≠ len(heights) | `ValidationError::MismatchedLengths` |
| `non_unit_normal` | ‖n‖ = 0.5 | `ValidationError::NonUnitNormal` |
| `zero_normal` | n = (0,0,0,0) | `ValidationError::NonUnitNormal` |
| `negative_height` | h = -1.0 | `ValidationError::NonPositiveHeight` |
| `zero_height` | h = 0.0 | `ValidationError::NonPositiveHeight` |
| `nan_in_normal` | n contains NaN | `ValidationError::NonFiniteNormal` |
| `inf_in_height` | h = +∞ | `ValidationError::NonFiniteHeight` |

### 5.2 Round-Trip Tests

| Test | Purpose |
|------|---------|
| `python_to_rust_and_back` | Polytope data survives FFI serialization |
| `witness_accessible` | Python can read all witness fields |
| `diagnostics_accessible` | Python can read all diagnostic fields |

### 5.3 HK&O End-to-End

```python
def test_hko_counterexample():
    polytope = load_hko_polytope()
    result = rust_viterbo_ffi.compute_capacity(polytope)

    assert abs(result.capacity - EXPECTED_HKO_CAPACITY) < 1e-4
    assert result.diagnostics.perturbation is not None  # Lagrangian, so perturbed
    verify_witness(result.witness, polytope)
```

## 6. Test Data

### 6.1 Tesseract (4D Cube)

```rust
fn tesseract() -> PolytopeHRep {
    let normals = vec![
        [1.0, 0.0, 0.0, 0.0],
        [-1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, -1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, -1.0, 0.0],
        [0.0, 0.0, 0.0, 1.0],
        [0.0, 0.0, 0.0, -1.0],
    ];
    let heights = vec![1.0; 8];
    PolytopeHRep { normals, heights }
}
```

**Properties:**
- 8 facets, 24 2-faces (16 Lagrangian, 8 non-Lagrangian)
- Requires perturbation for tube algorithm
- Known capacity from direct computation

### 6.2 4-Simplex

```rust
fn simplex_4d() -> PolytopeHRep {
    // Regular 4-simplex centered at origin
    // 5 facets, 10 2-faces
    // Vertices: (1,1,1,1), (1,-1,-1,1), (-1,1,-1,1), (-1,-1,1,1), (0,0,0,-√5+1)
    // (normalized and centered)
    todo!("Compute exact normals and heights")
}
```

### 6.3 Cross-Polytope (16-cell)

```rust
fn cross_polytope_4d() -> PolytopeHRep {
    // Dual of tesseract
    // 16 facets, normals are (±1,±1,±1,±1)/2 normalized
    // Vertices: (±1,0,0,0), (0,±1,0,0), (0,0,±1,0), (0,0,0,±1)
    todo!("Compute exact normals and heights")
}
```

## 7. Test Infrastructure

### 7.1 Tolerance Constants

```rust
const EPS_FEAS: f64 = 1e-10;      // Feasibility checks
const EPS_UNIT: f64 = 1e-12;      // Unit normal checks
const EPS_ACTION: f64 = 1e-10;    // Action comparisons
const EPS_CAPACITY: f64 = 1e-6;   // Capacity comparisons (regression)
const EPS_ROTATION: f64 = 0.01;   // Rotation pruning slack (in turns)
```

### 7.2 Test Helpers

```rust
fn verify_witness(witness: &WitnessOrbit, polytope: &PolytopeHRep) -> Result<(), String>;
fn approx_eq(a: f64, b: f64, eps: f64) -> bool;
fn scale_polytope(p: &PolytopeHRep, s: f64) -> PolytopeHRep;
fn apply_block_rotation(p: &PolytopeHRep, theta1: f64, theta2: f64) -> PolytopeHRep;
```

### 7.3 Test Organization

```
packages/rust_viterbo/
├── geom/src/lib.rs          # Unit tests for primitives
├── algorithm/src/lib.rs     # Unit tests for tube operations
├── algorithm/tests/         # Integration tests
│   ├── witness_validation.rs
│   ├── determinism.rs
│   └── known_polytopes.rs
└── ffi/tests/               # FFI tests (if any)

packages/python_viterbo/tests/
├── test_ffi_validation.py   # FFI input validation
├── test_hko_regression.py   # HK&O counterexample
└── test_ffi_roundtrip.py    # Serialization tests
```

## 8. Test Priorities

**Must have before shipping:**
1. All unit tests in §1 (fast, catch convention errors)
2. Witness verification (§2.1)
3. HK&O regression (§3.3)
4. FFI validation (§5.1)

**Should have:**
5. Scaling property test (§4.1)
6. Determinism tests (§2.2)
7. Other regression polytopes (§3.1, §3.2)

**Nice to have:**
8. Full property test suite (§4)
9. Symplectic invariance tests (§4.2)
10. Performance regression tests (not specified here)
