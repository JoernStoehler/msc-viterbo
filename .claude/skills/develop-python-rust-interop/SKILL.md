---
name: develop-python-rust-interop
description: Building or modifying Rust-Python FFI bindings using PyO3 and maturin. Use when exposing Rust algorithms to Python or fixing FFI issues.
---

# Rust-Python FFI

## Build

```bash
cd packages/python_viterbo
uv run maturin develop --manifest-path ../rust_viterbo/ffi/Cargo.toml
```

## Test

```bash
cd packages/python_viterbo
uv run pytest tests/test_ffi_capacity_hrep.py -v
```

## Design Principles

1. **Keep wrappers thin**: Convert types at boundary, delegate to library crates
2. **Validate at boundary**: Check inputs in FFI code, return structured errors
3. **Expose only working code**: No stubs or archived placeholders
4. **Match stubs to implementation**: `rust_viterbo_ffi.pyi` must accurately reflect actual API

## Key Files

- Rust FFI: `packages/rust_viterbo/ffi/src/lib.rs`
- Python stubs: `packages/python_viterbo/src/rust_viterbo_ffi.pyi`
- Tests: `packages/python_viterbo/tests/test_ffi_capacity_hrep.py`
