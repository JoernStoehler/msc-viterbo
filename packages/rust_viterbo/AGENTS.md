# AGENTS (rust_viterbo)
- Purpose: High-performance Rust library for symplectic geometry.
- Crates: `geom` (math), `algorithm` (different algorithms for the symplectic capacity), `ffi` (PyO3/Maturin bindings).

## Code Conventions
- Follow best practices for mathematically correct Rust code. 
- Pure functions with immutable types preferred.
- Use `nalgebra` for linear algebra operations.
- Commands:
  - `cargo fmt`
  - `cargo clippy --workspace --all-targets`
  - `cargo test --workspace`
  - `cargo test --release <filter>`
  - `cargo bench`

## Testing
- Follow best practices for unit testing in Rust.
- Cover happy paths, edge cases, error paths.

## Benchmarking & Profiling
- Follow best practices for benchmarking and profiling Rust code.
- Focus only on hotspots identified via profiling.
- Optimize only after profiling; document expectations, results, flags in comments near benchmarks.
- Document the why behind code changes, e.g. performance impact.

## Python FFI
- See `agent_docs/python-ffi-with-pyo3-maturin.md`

## Caching
- We share the target folder between git worktrees, which speeds up the first build time from minutes to seconds: `/workspaces/worktrees/shared/target` (set by worktree-new.sh).