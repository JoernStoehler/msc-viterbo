---
name: develop-python
description: Writing or testing Python code in packages/python_viterbo. Use when creating experiments, writing analysis stages, or working with the Python codebase.
---

# Python Development

## Package Structure

- Package: `viterbo`
- Experiments: `src/viterbo/experiments/<label>/`
- Each experiment: SPEC.md + stage_*.py files

## Commands

```bash
cd packages/python_viterbo

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

## Experiment Structure

**Always study example_pipeline first:**

`src/viterbo/experiments/example_pipeline/` is a complete teaching example demonstrating all conventions. Study it before creating new experiments.

**Standard layout:**
```
src/viterbo/experiments/<label>/
├── SPEC.md              # Research question, method, success criteria
├── stage_build.py       # Generate data
├── stage_analyze.py     # Compute results
└── stage_plot.py        # Create figures

config/<label>/
├── default.json         # Parameters
└── variant.json         # Alternative configs

data/<label>/            # Output artifacts
tests/test_<label>.py    # Tests
```

**Running stages:**
```bash
uv run python -m viterbo.experiments.<label>.stage_build
uv run python -m viterbo.experiments.<label>.stage_analyze
uv run python -m viterbo.experiments.<label>.stage_plot
```

**Reproduction must be obvious:**

Pattern should be self-evident from repo structure:

Good:
```bash
for cfg in config/polytope-families/*.json; do
  uv run python -m viterbo.experiments.polytope_families.stage_build "$cfg"
done
```

Bad: "Run with configs A, B, and C" (which configs? where?)

## Code Style

- **Docstrings**: Document inputs, outputs, shapes/dtypes
- **Pure functions**: Preferred when possible
- **Comments**: Explain WHY, not WHAT
