# AGENTS – Python Viterbo Package

You are in `packages/python_viterbo/`, which contains the Python orchestration, data pipelines, and ML code.

## Layout

- `pyproject.toml` – uv-managed Python project.
- `src/viterbo/` – main Python package namespace (currently holds placeholder helpers for smoke tests).
- `tests/` – lightweight pytest suite to ensure the toolchain stays green.

## Tooling and commands

- Use `uv` for dependency management and running commands.
- Typical commands:
  - `uv run --extra dev pytest` – run tests (pulls in the `dev` extra so `pytest` is available).
  - `uv run python -m viterbo` – run the main package entrypoint (if/when defined).

## Expectations

- Keep this package the “glue” layer: orchestration, pipelines, experiments, e2e tests. The current dummy helpers exist purely so the toolchain can be smoke-tested before real code lands.
- Heavy numerical work should live in Rust (`rust_viterbo`) and be called via the FFI crate.
