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
