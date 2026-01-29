# Python-Rust FFI Conventions

Patterns for Rust-Python interop via PyO3/maturin in `packages/rust_viterbo/ffi/`.

## Key Files

| File | Purpose |
|------|---------|
| `packages/rust_viterbo/ffi/src/lib.rs` | Rust FFI implementation |
| `packages/python_viterbo/src/rust_viterbo_ffi.pyi` | Python type stubs |
| `packages/python_viterbo/tests/test_ffi_capacity_hrep.py` | FFI tests |

## Build

```bash
cd /workspaces/worktrees/<task>/packages/python_viterbo
uv run maturin develop --manifest-path ../rust_viterbo/ffi/Cargo.toml
```

## Test

```bash
cd /workspaces/worktrees/<task>/packages/python_viterbo
uv run pytest tests/test_ffi_capacity_hrep.py -v
```

## Design Principles

1. **Keep wrappers thin**: Convert types at boundary, delegate to library crates
2. **Validate at boundary**: Check inputs in FFI code, return structured errors
3. **Expose only working code**: No stubs or archived placeholders
4. **Match stubs to implementation**: `.pyi` must accurately reflect actual API
