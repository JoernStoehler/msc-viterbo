---
name: develop-rust
description: Writing or testing Rust code in packages/rust_viterbo. Use when implementing algorithms, writing tests, fixing bugs, or working with the Rust codebase.
---

# Rust Development

## Reference Docs

- **Algorithm reference**: `docs/conventions/rust-algorithms.md` - crate organization, algorithm comparison
- **Testing conventions**: `docs/conventions/rust-testing.md` - test philosophy, modes, tolerances
- **Detailed test strategy**: See `develop-rust-tests` skill for algorithm-specific testing approach

## Commands

```bash
cd /workspaces/worktrees/<task>/packages/rust_viterbo

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

## Code Style

- Favor pure functions with immutable types
- Use `nalgebra` for linear algebra
- Use `approx` for floating-point comparisons
- Document "why" in comments
- Cover happy paths, edge cases, error paths

## Math <-> Code Correspondence

- Document mathematical propositions being tested
- Reference mathematical proofs in the thesis
- Use asserts/debug_asserts to close gap between Rust's type system and pure mathematics

## Cache Behavior

- **Codespace**: Each worktree builds independently (~60s cold start)
