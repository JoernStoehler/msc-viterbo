# AGENTS – Python Viterbo Package

You are in `packages/python_viterbo/`, which contains the Python orchestration, data pipelines, and ML code.

## Layout

- `pyproject.toml` – uv-managed Python project.
- `src/viterbo/` – main Python package namespace (currently holds placeholder helpers for smoke tests).
- `tests/` – lightweight pytest suite to ensure the toolchain stays green.

## Architecture context

- Treat this package as the orchestration layer: it glues together Rust implementations (via the `ffi` crate) and data/experiment pipelines.
- Any heavy computation should migrate into `packages/rust_viterbo` once stabilized; keep Python code thin so that experiments can be reproduced across worktrees.
- The package is also the integration test harness: end-to-end experiments should live here and call Rust/Lean components as needed.

## Tooling and commands

- Use `uv` for dependency management and running commands.
- Typical commands:
  - `uv run --extra dev pytest` – run tests (pulls in the `dev` extra so `pytest` is available).
  - `uv run python -m viterbo` – run the main package entrypoint (if/when defined).

## Expectations

- Keep this package the “glue” layer: orchestration, pipelines, experiments, e2e tests. The current dummy helpers exist purely so the toolchain can be smoke-tested before real code lands.
- Heavy numerical work should live in Rust (`rust_viterbo`) and be called via the FFI crate.
