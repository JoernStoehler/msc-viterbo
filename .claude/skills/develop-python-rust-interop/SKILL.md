---
name: develop-python-rust-interop
description: Building or modifying Rust-Python FFI bindings using PyO3 and maturin. Use when exposing Rust algorithms to Python or fixing FFI issues.
---

# Rust-Python FFI

See `docs/conventions/python-rust-ffi.md` for key files and design principles.

## Quick Reference

**Build:**
```bash
cd /workspaces/worktrees/<task>/packages/python_viterbo
uv run maturin develop --manifest-path ../rust_viterbo/ffi/Cargo.toml
```

**Test:**
```bash
uv run pytest tests/test_ffi_capacity_hrep.py -v
```

**Key files:**
- Rust: `packages/rust_viterbo/ffi/src/lib.rs`
- Stubs: `packages/python_viterbo/src/rust_viterbo_ffi.pyi`
