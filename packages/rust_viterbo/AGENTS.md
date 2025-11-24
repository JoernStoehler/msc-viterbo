# AGENTS – Rust Viterbo Package

You are in `packages/rust_viterbo/`, which contains the Rust code for the project, organized as a Cargo workspace.

## Goals

- Provide high-performance implementations of the core symplectic geometry and related math needed for the thesis.
- Expose these implementations to Python via a dedicated FFI crate.

## Layout

- `Cargo.toml` – workspace definition.
- `geom/` – library crate with core symplectic geometry structures and operations.
- `ffi/` – library crate providing PyO3/maturin bindings for Python.

Expect additional crates (e.g. algorithms, experiments) to be added later.

## Architecture context

- `geom` is the single source of truth for symplectic geometry primitives. Python, Lean, and future C++ bindings should all treat these APIs as canonical.
- `ffi` exposes stable, well-documented interfaces to `packages/python_viterbo`. Any breaking change must be reflected there first, then publicized via release notes/tests.
- When algorithms move from prototypes (Python) into Rust, keep the pure-Rust API clean so the Lean proofs can reference it without dragging in PyO3.

## Tooling and commands

- Use `cargo build`, `cargo test`, and `cargo fmt` directly; do not introduce custom wrappers unless an issue explicitly asks for it.
- When working on FFI, keep in mind that maturin will be used from the Python side to build and distribute Python bindings.
- Cargo caches are shared across worktrees via `.cargo/config.toml` (target-dir `../worktrees/shared/target`). Run `scripts/worktree-prepare.sh` here to create/fetch deps into that shared target once.

## Expectations

- Keep APIs small, well-documented, and stable enough that Python and Lean code can rely on them.
- Prefer simple, explicit implementations over clever ones.
- Document any non-obvious math decisions in code comments and, if cross-cutting, in this `AGENTS.md` or an appropriate design doc.
