---
name: develop-rust
description: Writing or testing Rust code in packages/rust_viterbo. Use when implementing algorithms, writing tests, fixing bugs, or working with the Rust codebase.
---

# Rust Development

## Crate Organization

- **geom**: Clean reference implementations (symplectic + euclidean geometry, 2D + 4D)
- **hk2017**: HK2017 algorithm (works on any bounded polytope with 0 ∈ int K)
- **billiard**: Billiard algorithm (Lagrangian products only)
- **tube**: Tube algorithm (non-Lagrangian polytopes)
- **ffi**: PyO3/Maturin bindings

## Philosophy: geom as Reference

Algorithms should use geom when it fits, but **copy and customize** when algorithm-specific needs diverge (e.g., different tolerances, extra fields).

**Duplication is acceptable when purposeful.** Value of geom: clean code to orient against, making deviations obvious and intentional.

## Commands

```bash
cd packages/rust_viterbo

# Test all modes
scripts/test.sh                  # Debug + release
scripts/test.sh --debug          # Debug only (with debug_assert!)
scripts/test.sh --release        # Release only (expensive tests)

# Standard tooling
cargo test --workspace           # Debug tests
cargo test --release --workspace # Release tests
cargo clippy --workspace         # Lint
cargo fmt --all                  # Format
cargo bench                      # Benchmarks
```

## Testing Philosophy: Tests as Propositions

Write tests that verify mathematical propositions, not just "does it run without crashing."

**Good**: `prop_scaling_law` - "∀K, ∀λ>0: c(λK) = λ²c(K)"
**Bad**: `test_random_stuff` - "call function, check no panic"

### Structure Example

```rust
/// Proposition: For all valid polytopes K, c(K) > 0.
///
/// Tested on: cross-polytope, 24-cell, asymmetric variants.
#[test]
fn prop_capacity_positive() {
    for (name, k) in test_polytopes() {
        let c = compute_capacity(&k).expect(&format!("{} should succeed", name));
        assert!(c > 0.0, "{}: c(K) = {} violates c(K) > 0", name, c);
    }
}
```

## Test Modes

**Debug mode** (default `cargo test`):
- Tests exercising `debug_assert!()` checks
- Tests verifying internal invariants
- Most unit tests

**Release mode** (`cargo test --release`):
- Expensive tests (only verify output correctness)
- Property tests with many iterations
- Tests where computation speed matters

**Mark tests with:**
```rust
#[cfg_attr(debug_assertions, ignore)]      // Release only
#[cfg_attr(not(debug_assertions), ignore)] // Debug only
```

## Testing Levels

1. **Debug assertions** (`debug_assert!`): Expensive internal invariants
   ```rust
   debug_assert!((n.norm() - 1.0).abs() < 1e-10, "Normal must be unit");
   ```

2. **Runtime assertions** (`assert!`): Always-checked conditions
   ```rust
   assert_eq!(normals.len(), heights.len(), "Must have same count");
   ```

3. **Unit tests** (`#[test]`): Individual functions
   ```rust
   #[test]
   fn test_symplectic_form_antisymmetric() { ... }
   ```

4. **Property tests** (proptest): Random inputs
   ```rust
   proptest! {
       #[test]
       fn prop_symplectic_antisymmetric(x in uniform_vector4(), y in uniform_vector4()) {
           let omega_xy = symplectic_form(&x, &y);
           let omega_yx = symplectic_form(&y, &x);
           prop_assert!((omega_xy + omega_yx).abs() < 1e-10);
       }
   }
   ```

5. **Integration tests** (`tests/`): Full algorithm on realistic inputs
   ```rust
   #[test]
   fn test_cross_polytope_capacity() {
       let hrep = fixtures::unit_cross_polytope();
       let result = compute_capacity(&hrep).expect("should compute");
       assert_relative_eq!(result.capacity, 1.0, epsilon = 0.01);
   }
   ```

## Numerical Tolerances

Use `approx` crate for floating-point comparisons:

```rust
use approx::assert_relative_eq;

assert_relative_eq!(actual, expected, epsilon = 1e-10);
assert_relative_eq!(actual, expected, max_relative = 0.01); // 1% relative error
```

**Note:** Tolerance values are ad-hoc guesses for numerical error accumulation, not well-motivated constants. Use judgment.

## Fixtures and Test Data

**Named constants** for standard objects:
```rust
pub fn unit_cross_polytope() -> PolytopeHRep { ... }
pub fn unit_24_cell() -> PolytopeHRep { ... }
```

**Parameterized families:**
```rust
pub fn scaled_cross_polytope(lambda: f64) -> PolytopeHRep { ... }
pub fn asymmetric_cross_polytope(seed: u64) -> PolytopeHRep { ... }
```

**Random generators:**
- Must be deterministic (seeded)
- Document distribution (NOT "uniform on S³" unless using Gaussian normalization)
- Document rejection criteria and empirical success rates

Example:
```rust
/// Generate random H-rep. Returns None on rejection.
///
/// # Success rates (empirical, 10k seeds)
/// - n=6: ~31%
/// - n=8: ~32%
/// - n=10: ~12%
pub fn random_hrep(n_facets: usize, min_omega: f64, max_coord: f64, seed: u64)
    -> Option<PolytopeHRep>
```

## Code Style

- Favor pure functions with immutable types
- Use nalgebra for linear algebra
- Document "why" in comments, not "what"
- Cover happy paths, edge cases, error paths

## Cache Behavior

- **Local env**: Shared target dir at `/workspaces/worktrees/shared/target` (via `CARGO_TARGET_DIR`)
- **Codespace**: Each worktree builds independently (~60s cold start)
