---
name: debugging-numerical
description: Numerical debugging and tolerance handling. Reference for tolerance constants and comparison patterns.
---

# Numerical Debugging

## Tolerance Constants

See single source of truth:
- `crates/geom2d/src/tolerances.rs`
- `crates/geom4d/src/tolerances.rs`

## Float Comparison

Use `approx` crate, not `==`:
```rust
use approx::assert_relative_eq;
assert_relative_eq!(computed, expected, epsilon = EPS);
```
