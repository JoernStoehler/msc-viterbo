---
name: rust-conventions
description: Work on Rust crates in packages/rust_viterbo. Use for crate layout, commands (fmt/clippy/test/bench), and coding conventions.
---

# Rust Conventions (rust_viterbo)

## Crates

- `geom` — shared geometry library (symplectic + euclidean, 2D + 4D)
- `hk2017` — HK2017 permutation enumeration algorithm
- `tube` — tube algorithm (branch-and-bound)
- `billiard` — billiard algorithm (Lagrangian products)
- `ffi` — PyO3/Maturin bindings for Python

## The geom Crate and Customization

`geom` provides **clean reference implementations** of fundamental geometry. Algorithm crates should:

- **Use geom** when the standard implementation fits
- **Copy and customize** when algorithm-specific needs diverge (e.g., different tolerances, extra fields)

Duplication is acceptable when purposeful. The value of `geom` is providing clean code to orient against — making deviations obvious and intentional. Don't force algorithms to use `geom` when a customized version serves them better.

## Commands

- `cargo fmt`
- `cargo clippy --workspace --all-targets`
- `cargo test --workspace`
- `cargo test --release <filter>`
- `cargo bench`

## Conventions

- Favor pure functions with immutable types.
- Follow best practices for mathematically correct Rust code.
- Use `nalgebra` for linear algebra operations.

## Testing and profiling

- Cover happy paths, edge cases, error paths.
- Benchmark only after profiling identifies hotspots.
- Document why changes are made (e.g., performance impact).

## Caching

- Shared target dir: `/workspaces/worktrees/shared/target` (set by worktree script).
