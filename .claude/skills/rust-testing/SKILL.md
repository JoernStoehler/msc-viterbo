# Rust Testing Conventions

Guidelines for testing Rust code in this project, with emphasis on property-based testing and mathematical correctness.

## Philosophy: Tests as Propositions

Tests should verify mathematical propositions, not just "does it run without crashing".

**Good**: `prop_scaling_law` - "∀K, ∀λ>0: c(λK) = λ²c(K)"
**Bad**: `test_random_stuff` - "call function, check no panic"

### Structure

```rust
/// Proposition: For all valid polytopes K, c(K) > 0.
///
/// Tested on: cross-polytope, 24-cell, asymmetric variants.
#[test]
fn prop_capacity_positive() {
    for (name, k) in test_polytopes() {
        let c = tube_capacity(&k).expect(&format!("{} should succeed", name));
        assert!(c.capacity > 0.0, "{}: c(K) = {} violates c(K) > 0", name, c.capacity);
    }
}
```

## Testing Levels

### 1. Debug Assertions (`debug_assert!`)

Use for internal invariants that are expensive to check in production:

```rust
fn reeb_vector(n: &Vector4<f64>, h: f64) -> Vector4<f64> {
    debug_assert!(h > 0.0, "Height must be positive");
    debug_assert!((n.norm() - 1.0).abs() < 1e-10, "Normal must be unit");
    apply_quat_i(n) * (2.0 / h)
}
```

### 2. Runtime Assertions (`assert!`)

Use for conditions that must always hold, even in release:

```rust
pub fn new(normals: Vec<Vector4<f64>>, heights: Vec<f64>) -> Self {
    assert_eq!(normals.len(), heights.len(), "Must have same number of normals and heights");
    // ...
}
```

### 3. Unit Tests (`#[test]`)

Test individual functions and invariants:

```rust
#[test]
fn test_quat_i_squared_is_minus_identity() {
    let i = quat_i();
    let i_squared = i * i;
    assert_relative_eq!(i_squared, -Matrix4::identity(), epsilon = EPS);
}
```

### 4. Property-Based Tests (proptest)

For properties that should hold across many random inputs:

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn prop_symplectic_form_antisymmetric(
        x in uniform_vector4(),
        y in uniform_vector4()
    ) {
        let omega_xy = symplectic_form(&x, &y);
        let omega_yx = symplectic_form(&y, &x);
        prop_assert!((omega_xy + omega_yx).abs() < 1e-10);
    }
}
```

### 5. Integration Tests (`tests/`)

Test the full algorithm on realistic inputs:

```rust
#[test]
fn test_cross_polytope_capacity() {
    let hrep = fixtures::unit_cross_polytope();
    let result = tube_capacity(&hrep).expect("should compute");
    assert_relative_eq!(result.capacity, 1.0, epsilon = 0.01);
}
```

## Fixtures and Test Data

### Named Constants

For standard mathematical objects:

```rust
pub fn unit_cross_polytope() -> PolytopeHRep { ... }
pub fn unit_24_cell() -> PolytopeHRep { ... }
```

### Parameterized Families

```rust
pub fn scaled_cross_polytope(lambda: f64) -> PolytopeHRep { ... }
pub fn asymmetric_cross_polytope(seed: u64) -> PolytopeHRep { ... }
```

### Random Generators

Must be deterministic (seeded) and document:
- Distribution (NOT "uniform on S³" unless using Gaussian normalization)
- Rejection criteria and rates

```rust
/// Generate random H-rep. Returns None on rejection.
///
/// # Success rates (empirical, 10k seeds)
/// - n=6: ~31%
/// - n=8: ~32%
/// - n=10: ~12%
pub fn random_hrep(n_facets: usize, min_omega: f64, max_coord: f64, seed: u64) -> Option<PolytopeHRep>
```

### Diagnostics

When a generator has low success rate, add a diagnostic version:

```rust
pub enum RejectionReason {
    NearLagrangian,
    Unbounded,
    TooFewVertices,
    // ...
}

pub fn random_hrep_diagnostic(...) -> Result<PolytopeHRep, RejectionReason>
```

## proptest Setup

Add to `Cargo.toml`:

```toml
[dev-dependencies]
proptest = "1.4"
```

Define strategies for your domain types:

```rust
use proptest::prelude::*;

fn uniform_vector4() -> impl Strategy<Value = Vector4<f64>> {
    (any::<f64>(), any::<f64>(), any::<f64>(), any::<f64>())
        .prop_map(|(a, b, c, d)| Vector4::new(a, b, c, d))
}

fn valid_polytope() -> impl Strategy<Value = PolytopeHRep> {
    // Use fixtures or filtered generation
    prop_oneof![
        Just(fixtures::unit_cross_polytope()),
        Just(fixtures::unit_24_cell()),
        (0u64..1000).prop_filter_map("asymmetric", |seed| {
            fixtures::random_hrep(8, 0.01, 100.0, seed)
        }),
    ]
}
```

## Numerical Tolerances

Use `approx` crate for floating-point comparisons:

```rust
use approx::assert_relative_eq;

assert_relative_eq!(actual, expected, epsilon = 1e-10);
assert_relative_eq!(actual, expected, max_relative = 0.01); // 1% relative error
```

Define project-wide constants:

```rust
// constants.rs
pub const EPS: f64 = 1e-10;           // General tolerance
pub const EPS_LAGRANGIAN: f64 = 1e-8; // For detecting Lagrangian 2-faces
pub const EPS_CLOSURE: f64 = 1e-6;    // For orbit closure (accumulated error)
```

## Test Organization

```
tube/
├── src/
│   ├── lib.rs           # Doctests for public API
│   ├── algorithm.rs     # Unit tests in `mod tests { ... }`
│   └── fixtures.rs      # Fixture tests
└── tests/
    ├── integration.rs   # Full algorithm tests
    ├── orbit_invariants.rs  # Mathematical invariant tests
    └── flow_map_tests.rs    # Robustness tests
```

## Running Tests

```bash
# All tests
cargo test -p tube

# Specific test
cargo test -p tube --lib fixtures::tests::test_24_cell_valid

# With output
cargo test -p tube -- --nocapture

# Property tests with more cases
PROPTEST_CASES=1000 cargo test -p tube
```
