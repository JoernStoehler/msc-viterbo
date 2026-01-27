---
name: ffi-pyo3-maturin
description: Build or modify the Rust-Python FFI using PyO3+maturin. Use for binding builds, smoke tests, and boundary validation workflow.
---

# PyO3 + maturin FFI Workflow

## Build

```bash
cd packages/python_viterbo && uv run maturin develop --manifest-path ../rust_viterbo/ffi/Cargo.toml
```

## Test

```bash
cd packages/python_viterbo && uv run pytest tests/test_ffi_capacity_hrep.py -v
```

## API Overview

The FFI exposes:

- `hk2017_capacity_hrep(normals, heights, use_graph_pruning=False) -> Hk2017Result`: Compute EHZ capacity using the HK2017 combinatorial formula
- `symplectic_form_4d(a, b) -> float`: Compute the standard symplectic form in R^4

## Design Principles

1. **Keep wrappers thin**: Convert types at the boundary, delegate to library crates
2. **Validate at boundary**: Check inputs in FFI code, return structured errors
3. **Expose only working code**: No stubs or archived placeholders - if it's not implemented, don't expose it
4. **Match stubs to implementation**: `rust_viterbo_ffi.pyi` must accurately reflect the actual API

## Files

- Rust FFI: `packages/rust_viterbo/ffi/src/lib.rs`
- Python stubs: `packages/python_viterbo/src/rust_viterbo_ffi.pyi`
- Tests: `packages/python_viterbo/tests/test_ffi_capacity_hrep.py`
