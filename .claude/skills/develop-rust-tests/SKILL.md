---
name: develop-rust-tests
description: Comprehensive testing strategy for Rust capacity algorithms. Use when writing tests for HK2017, Tube, Billiard, or validating algorithm correctness.
---

# Algorithm Testing Strategy

This skill extends `develop-rust` with the comprehensive testing strategy for capacity algorithms (HK2017, Tube, Billiard).

## Core Principle

All algorithms should share the same test structure. Tests verify mathematical propositions, not just "does it run."

## Test Polytope Sets

### Diversity Requirement

Use a **large, diverse** set of polytopes including random ones. This avoids accidentally relying on unstated properties shared by all test cases.

```rust
fn test_polytopes() -> Vec<(String, PolytopeHRep)> {
    vec![
        // Fixed known polytopes
        ("cross_polytope".into(), fixtures::unit_cross_polytope()),
        ("24_cell".into(), fixtures::unit_24_cell()),
        ("tesseract".into(), fixtures::unit_tesseract()),

        // Parameterized families
        ("asymmetric_0".into(), fixtures::asymmetric_cross_polytope(0)),
        ("asymmetric_1".into(), fixtures::asymmetric_cross_polytope(1)),

        // Random polytopes (seeded for reproducibility)
        ...(0..100).filter_map(|seed| {
            fixtures::random_hrep(8, 0.1, seed)
                .map(|p| (format!("random_{}", seed), p))
        }).collect::<Vec<_>>(),
    ]
}
```

### Lagrangian Products (for Billiard)

```rust
fn test_lagrangian_products() -> Vec<(String, LagrangianProduct)> {
    vec![
        ("square_square".into(), square() * square()),
        ("triangle_triangle".into(), triangle() * triangle()),
        ("pentagon_pentagon".into(), pentagon() * pentagon()),
        // Random n-gon × m-gon products
        ...(3..=8).flat_map(|n| (3..=8).map(move |m| {
            (format!("{}gon_{}gon", n, m), regular_ngon(n) * regular_ngon(m))
        })).collect::<Vec<_>>(),
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
            assert_relative_eq!(c_k, c_phi_k, epsilon = 1e-8,
                "{}: c(K) = {} but c(φK) = {}", name, c_k, c_phi_k);
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
        let scaled = scale_polytope(&k, 1.1);  // Slightly larger
        assert!(compute_capacity(&k) <= compute_capacity(&scaled),
            "{}: monotonicity violated", name);
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

### Continuity

```rust
/// Proposition: Small perturbations → small capacity changes
#[test]
fn prop_continuity() {
    for (name, k) in test_polytopes() {
        let c_k = compute_capacity(&k);
        let perturbed = perturb_polytope(&k, 0.001);  // Small Hausdorff distance
        let c_perturbed = compute_capacity(&perturbed);
        // Expect capacity change proportional to perturbation
        assert!((c_k - c_perturbed).abs() < 0.1 * c_k,
            "{}: discontinuity detected", name);
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
        ("cross_polytope", cross_polytope(), 1.0),       // Empirical
    ];
    for (name, k, expected) in cases {
        let actual = compute_capacity(&k);
        assert_relative_eq!(actual, expected, epsilon = 0.01,
            "{}: expected {} but got {}", name, expected, actual);
    }
}
```

## Minimum Orbit Tests

The witness orbit returned by algorithms must satisfy:

### Geometric Properties

```rust
/// Proposition: Witness is a valid closed affine curve on ∂K
#[test]
fn prop_orbit_geometric_validity() {
    for (name, k) in test_polytopes() {
        let (capacity, witness) = compute_capacity_with_witness(&k);

        // Is closed
        assert!(witness.is_closed(), "{}: orbit not closed", name);

        // Is affine (piecewise linear)
        assert!(witness.is_affine(), "{}: orbit not affine", name);

        // Breakpoints lie on ∂K
        for bp in witness.breakpoints() {
            assert!(is_on_boundary(&k, bp),
                "{}: breakpoint {:?} not on boundary", name, bp);
        }

        // Segments lie on ∂K (both endpoints share at least one facet)
        for seg in witness.segments() {
            let shared = shared_facets(&k, seg.start, seg.end);
            assert!(!shared.is_empty(),
                "{}: segment endpoints don't share a facet", name);
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

        // Action via integral definition (easy for affine curves)
        let action = compute_action(&witness);
        assert_relative_eq!(action, capacity, epsilon = 1e-8,
            "{}: action {} ≠ capacity {}", name, action, capacity);

        // Period
        let period = witness.period();
        assert_relative_eq!(period, capacity, epsilon = 1e-8,
            "{}: period {} ≠ capacity {}", name, period, capacity);
    }
}
```

### Velocity Constraints

```rust
/// Proposition: Velocity along each segment is a convex combination
/// of Reeb velocities 2/h_i J n_i of the facets the segment lies on.
#[test]
fn prop_velocity_is_reeb_combination() {
    for (name, k) in test_polytopes() {
        let (_, witness) = compute_capacity_with_witness(&k);

        for seg in witness.segments() {
            let velocity = seg.velocity();
            let facets = shared_facets(&k, seg.start, seg.end);
            let reeb_vecs: Vec<_> = facets.iter()
                .map(|f| reeb_velocity(&k, *f))
                .collect();

            // velocity must be in the conic hull of reeb_vecs
            assert!(is_in_conic_hull(&velocity, &reeb_vecs),
                "{}: velocity not a valid Reeb combination", name);
        }
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

        // Filter to successful computations
        let successes: Vec<_> = results.iter()
            .filter_map(|(alg, r)| r.as_ref().ok().map(|c| (*alg, *c)))
            .collect();

        // All successful algorithms should agree
        if successes.len() >= 2 {
            let (ref_alg, ref_cap) = successes[0];
            for (alg, cap) in &successes[1..] {
                assert_relative_eq!(ref_cap, cap, epsilon = 0.01,
                    "{}: {} gives {} but {} gives {}",
                    name, ref_alg, ref_cap, alg, cap);
            }
        }
    }
}
```

## Algorithm-Specific Internal Tests

Each algorithm has internal invariants worth testing:

### HK2017

- KKT solution satisfies constraints
- β weights are non-negative
- Optimal permutation produces valid orbit

### Tube

- Tube rotation is non-decreasing along extensions
- Tube endpoint sets are non-empty until pruning
- Fixed point solver converges

### Billiard

- Bounce points lie on polygon boundaries
- Reflection rule satisfied at each bounce
- LP solution is feasible

## Building Block Tests

Test algorithm sub-components independently:

```rust
// Tube: rotation increment is correct
#[test]
fn prop_rotation_increment_formula() { ... }

// Tube: flow map composition is associative
#[test]
fn prop_flow_map_composition() { ... }

// HK2017: Hessian structure matches formula
#[test]
fn prop_hessian_structure() { ... }
```

## Using proptest

For "for all" statements, use proptest to sample the domain:

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn prop_scaling_law(
        polytope in arbitrary_polytope(),
        lambda in 0.1f64..10.0,
    ) {
        let c_k = compute_capacity(&polytope)?;
        let c_lambda_k = compute_capacity(&scale(&polytope, lambda))?;
        prop_assert!((c_lambda_k - lambda * lambda * c_k).abs() < 1e-6);
    }
}
```

## Test Organization

```
crate/
├── src/
│   └── lib.rs
└── tests/
    ├── capacity_axioms.rs      # Symplecto, monotone, scaling
    ├── orbit_properties.rs     # Geometric validity, action=cap
    ├── literature_values.rs    # Known ground truth
    ├── cross_validation.rs     # Algorithm agreement
    └── internals.rs            # Algorithm-specific checks
```
