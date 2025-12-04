# Python FFI (PyO3 + maturin)
- Purpose: Provide Python bindings for the high performance Rust library `rust_viterbo`.

## Build
- `cd packages/python_viterbo && uv run maturin develop --manifest-path ../rust_viterbo/Cargo.toml`
- Test with: `cd packages/python_viterbo && uv run pytest -q tests/smoke`

## Code Conventions
- Keep PyO3 wrappers thin; convert types near the boundary.
- Avoid breaking Python-facing APIs without coordinating with python_viterbo.
- Avoid complex ownership/lifetime logic in PyO3 code.