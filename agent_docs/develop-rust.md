# Developing in Rust
- Package: `packages/rust_viterbo`
- Goal: High-performance symplectic geometry primitives and algorithms; expose stable bindings for Python via the `ffi` crate.
- Toolchain: we pinned a recent-ish version.
- Caching: Shared target dir at `/workspaces/worktrees/shared/target` to reduce rebuild times.
- Commands: `cargo fmt`, `cargo clippy --workspace --all-targets`, `cargo test --workspace`.
- Creates: `geom` crate with core geometry; `algorithm` with algorithms for the EHZ capacity; `ffi` crate with Python FFI bindings.

## Conventions
- Prefer straightforward, idiomatic Rust solutions over clever or complex ones.
- Use Rust's module system to organize code; keep related functionality together.
- Use types and functions similar to the thesis writeup where applicable, and document differences in code comments.
- Write unit tests to catch bugs and regressions early. Cover happy paths, edge cases, and error paths. Use fixture data where applicable.
- Use analysis tools: `cargo clippy`, `cargo fmt`, `cargo check`, `cargo test`, etc.
- Document the "why" behind design decisions in code comments and docstrings.
- Write in a mathy functional programming style with immutable data structures where sensible; avoid unnecessary mutability.
- Only optimize code for performance after benchmarking, profiling, identifying the hotspots, and discussing with the project owner.
- Use the `ffi` crate to expose stable, ergonomic Python bindings. Python uses `maturin` to build the bindings. 
- Use `nalgebra` for linear algebra operations.

