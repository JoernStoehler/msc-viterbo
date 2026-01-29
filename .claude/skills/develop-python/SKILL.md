---
name: develop-python
description: Writing or testing Python code in packages/python_viterbo. Use when creating experiments, writing analysis stages, or working with the Python codebase.
---

# Python Development

## Reference Docs

- **Experiment conventions**: `docs/conventions/python-experiments.md` - structure, stages, reproduction
- **FFI patterns**: `docs/conventions/python-rust-ffi.md` - building and testing FFI

## Package Structure

- Package: `viterbo`
- Experiments: `src/viterbo/experiments/<label>/`
- Each experiment: `SPEC.md` + `stage_*.py` files

## Commands

```bash
cd /workspaces/worktrees/<task>/packages/python_viterbo

# Setup (first time)
uv sync --extra dev

# Testing
uv run pytest                    # All tests
uv run pytest tests/test_foo.py  # Specific file

# Linting
uv run ruff format .             # Format
uv run ruff check --fix .        # Lint
uv run pyright                   # Type check
```

## Running Experiment Stages

```bash
cd /workspaces/worktrees/<task>/packages/python_viterbo
uv run python -m viterbo.experiments.<label>.stage_build
uv run python -m viterbo.experiments.<label>.stage_analyze
uv run python -m viterbo.experiments.<label>.stage_plot
```

## Code Style

- **Docstrings**: Document inputs, outputs, shapes/dtypes
- **Pure functions**: Preferred when possible
- **Comments**: Explain WHY, not WHAT
- **KISS**: Avoid clever tricks and premature abstractions
- **Fast dev cycle**: Break interfaces and refactor freely; no external users
