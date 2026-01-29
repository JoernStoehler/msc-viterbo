# Rust Testing Conventions

Testing philosophy and patterns for `packages/rust_viterbo/`.

## Philosophy: Tests as Propositions

Write tests that verify mathematical propositions, not just "does it run without crashing."

**Good**: `prop_scaling_law` - "∀K, ∀λ>0: c(λK) = λ²c(K)"
**Bad**: `test_random_stuff` - "call function, check no panic"

## Test Modes

**Debug mode** (default `cargo test`):
- Tests exercising `debug_assert!()` checks
- Tests verifying internal invariants
- Most unit tests

**Release mode** (`cargo test --release`):
- Expensive tests that cannot run in debug mode within reasonable time
- Only move tests after profiling the test suite to identify slow tests
- Must not require debug assertions

**Annotations:**
```rust
#[cfg_attr(debug_assertions, ignore)]      // Release only
#[cfg_attr(not(debug_assertions), ignore)] // Debug only
```

## Testing Levels

1. **Debug assertions** (`debug_assert!`): Semi-expensive internal invariants
2. **Runtime assertions** (`assert!`): Always-checked conditions
3. **Unit tests** (`#[test]`): Expensive functions, run once per suite
4. **Property tests** (proptest): Random inputs, multiple iterations
5. **Integration tests** (`tests/`): Full algorithm on realistic inputs

## Numerical Tolerances

Use `approx` crate:

```rust
use approx::assert_relative_eq;
assert_relative_eq!(actual, expected, epsilon = 1e-10);
assert_relative_eq!(actual, expected, max_relative = 0.01); // 1% relative
```

Tolerance values are informed guesses. Document reasoning in comments.

## Fixtures

- Named constants: `unit_cross_polytope()`, `unit_24_cell()`
- Parameterized families: `scaled_cross_polytope(lambda)`
- Random generators: Must be seeded, document distribution and rejection rates

---

# Algorithm Testing Strategy

Comprehensive testing for capacity algorithms (HK2017, Tube, Billiard).

## Test Polytope Sets

Use a **large, diverse** set including random polytopes. Avoids accidentally relying on unstated properties shared by all test cases.

```rust
fn test_polytopes() -> Vec<(String, PolytopeHRep)> {
    vec![
        // Fixed known polytopes
        ("cross_polytope".into(), fixtures::unit_cross_polytope()),
        ("24_cell".into(), fixtures::unit_24_cell()),
        // Parameterized families
        ("asymmetric_0".into(), fixtures::asymmetric_cross_polytope(0)),
        // Random polytopes (seeded for reproducibility)
        ...(0..100).filter_map(|seed| {
            fixtures::random_hrep(8, 0.1, seed)
                .map(|p| (format!("random_{}", seed), p))
        }).collect::<Vec<_>>(),
    ]
}
```

## Capacity Axiom Tests

### Symplectomorphism Invariance

```rust
/// Proposition: c(φK) = c(K) for all linear symplectomorphisms φ.
#[test]
fn prop_symplectomorphism_invariance() {
    for (name, k) in test_polytopes() {
        let c_k = compute_capacity(&k);
        for phi in test_symplectomorphisms() {  // Include random ones!
            let phi_k = apply_symplectomorphism(&k, &phi);
            let c_phi_k = compute_capacity(&phi_k);
            assert_relative_eq!(c_k, c_phi_k, epsilon = 1e-8);
        }
    }
}
```

### Monotonicity

```rust
/// Proposition: K ⊆ L ⟹ c(K) ≤ c(L)
#[test]
fn prop_monotonicity() {
    for (name, k) in test_polytopes() {
        let scaled = scale_polytope(&k, 1.1);
        assert!(compute_capacity(&k) <= compute_capacity(&scaled));
    }
}
```

### Scaling Law

```rust
/// Proposition: c(λK) = λ² c(K) for λ > 0
#[test]
fn prop_scaling() {
    for (name, k) in test_polytopes() {
        for lambda in [0.5, 1.0, 2.0, 3.7] {
            let c_k = compute_capacity(&k);
            let c_lambda_k = compute_capacity(&scale_polytope(&k, lambda));
            assert_relative_eq!(c_lambda_k, lambda * lambda * c_k, epsilon = 1e-8);
        }
    }
}
```

### Literature Values

```rust
/// Proposition: Algorithm matches known literature values
#[test]
fn prop_literature_values() {
    let cases = vec![
        ("tesseract [-1,1]^4", tesseract(), 4.0),        // HK2017 Example 4.6
        ("pentagon×pentagon_90", hko_counterexample(), 3.441),  // HK-O 2024
    ];
    for (name, k, expected) in cases {
        let actual = compute_capacity(&k);
        assert_relative_eq!(actual, expected, epsilon = 0.01);
    }
}
```

## Minimum Orbit Tests

### Geometric Validity

```rust
/// Proposition: Witness is a valid closed affine curve on ∂K
#[test]
fn prop_orbit_geometric_validity() {
    for (name, k) in test_polytopes() {
        let (capacity, witness) = compute_capacity_with_witness(&k);
        assert!(witness.is_closed());
        assert!(witness.is_affine());
        for bp in witness.breakpoints() {
            assert!(is_on_boundary(&k, bp));
        }
    }
}
```

### Action-Capacity-Period Equality

```rust
/// Proposition: action(orbit) = capacity = period
#[test]
fn prop_action_equals_capacity() {
    for (name, k) in test_polytopes() {
        let (capacity, witness) = compute_capacity_with_witness(&k);
        let action = compute_action(&witness);
        assert_relative_eq!(action, capacity, epsilon = 1e-8);
    }
}
```

## Cross-Algorithm Validation

```rust
/// Proposition: All algorithms agree on overlapping domains
#[test]
fn prop_algorithms_agree() {
    for (name, k) in test_polytopes() {
        let results = vec![
            ("hk2017", hk2017::compute_capacity(&k)),
            ("tube", tube::compute_capacity(&k)),
        ];
        let successes: Vec<_> = results.iter()
            .filter_map(|(alg, r)| r.as_ref().ok().map(|c| (*alg, *c)))
            .collect();
        if successes.len() >= 2 {
            let (_, ref_cap) = successes[0];
            for (_, cap) in &successes[1..] {
                assert_relative_eq!(ref_cap, cap, epsilon = 0.01);
            }
        }
    }
}
```

## Test Organization

```
crate/
├── src/lib.rs
└── tests/
    ├── capacity_axioms.rs      # Symplecto, monotone, scaling
    ├── orbit_properties.rs     # Geometric validity, action=cap
    ├── literature_values.rs    # Known ground truth
    ├── cross_validation.rs     # Algorithm agreement
    └── internals.rs            # Algorithm-specific checks
```
