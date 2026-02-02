# Rust Testing Conventions

Testing philosophy for `packages/rust_viterbo/`.

## Why We Test

Tests verify mathematical properties. Math proofs use dependent types (values in types); Rust doesn't. Tests and asserts bridge this gap—they encode properties the type system can't express.

Not for API design (TDD) or regression prevention (research code, not production).

## Philosophy: Tests as Propositions

Write tests that verify mathematical propositions, not just "does it run without crashing."

**Good**: `prop_scaling_law` - "∀K, ∀λ>0: c(λK) = λ²c(K)"
**Bad**: `test_random_stuff` - "call function, check no panic"

## Test Modes

**Debug mode** (`cargo test`): Tests exercising `debug_assert!()`, internal invariants.

**Release mode** (`cargo test --release`): Expensive tests that timeout in debug mode.

## Rust vs Python Tests

| Aspect | Rust | Python |
|--------|------|--------|
| Speed | Faster | Slower (but calls Rust via FFI) |
| Setup | More boilerplate | More concise |
| Libraries | nalgebra, proptest | numpy, hypothesis, pytest |
| Best for | Fast tests, internal invariants | Expensive tests, visualization, exploration |

Use Python for tests that benefit from hypothesis, visualization, or quick iteration. Use Rust for tests that need internal access or must run quickly.

```rust
#[cfg_attr(debug_assertions, ignore)]      // Release only
#[cfg_attr(not(debug_assertions), ignore)] // Debug only
```

## What to Test (Capacity Algorithms)

Test mathematical axioms, not just "it runs":

- **Symplectomorphism invariance**: c(φK) = c(K)
- **Monotonicity**: K ⊆ L ⟹ c(K) ≤ c(L)
- **Scaling**: c(λK) = λ²c(K)
- **Literature values**: Match known results (HK2017 examples, HK-O counterexample)
- **Cross-algorithm agreement**: HK2017 and Tube agree on shared domain
- **Orbit validity**: Witness is closed, piecewise-affine, on ∂K

See `geom4d/tests/` for examples.

## Test Polytope Sets

Use diverse sets including random polytopes—avoids relying on unstated properties shared by all test cases. See `tube/src/fixtures.rs`.

## Tolerances

Document reasoning for tolerance values. They're informed guesses for numerical error accumulation.
