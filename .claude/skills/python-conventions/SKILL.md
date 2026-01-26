---
name: python-conventions
description: Work on Python experiments in packages/python_viterbo. Use for layout conventions, stage entrypoints, lint/test commands, and asset/plot handling.
---

# Python Conventions (python_viterbo)

## Example: polytope-database

Before reading abstract conventions, look at a concrete example:

```
packages/python_viterbo/
├── src/viterbo/experiments/polytope_database/
│   ├── __init__.py
│   ├── SPEC.md              # Research question, columns, invariants
│   └── stage_build.py       # Builds stub DataFrame, saves to Parquet
├── data/polytope-database/
│   └── stub.parquet         # Output artifact
└── tests/test_polytope_database.py
```

Run it: `uv run python -m viterbo.experiments.polytope_database.stage_build`
Test it: `uv run pytest tests/test_polytope_database.py`

This experiment demonstrates: SPEC.md, stage entrypoint, data output, tests.

## Directory layout

All paths relative to `packages/python_viterbo/`:

| Artifact | Path | Example |
|----------|------|---------|
| Experiment code | `src/viterbo/experiments/<label>/` | `experiments/polytope_database/` |
| Stage entrypoints | `src/viterbo/experiments/<label>/stage_<name>.py` | `stage_build.py` |
| Experiment spec | `src/viterbo/experiments/<label>/SPEC.md` | Required for non-trivial experiments |
| Data artifacts | `data/<label>/` | `data/polytope-database/stub.parquet` |
| Configs | `config/<label>/<variant>.json` | Optional, for parameterized runs |
| Tests | `tests/test_<label>.py` | `tests/test_polytope_database.py` |
| Thesis assets | `../latex_viterbo/assets/<label>/` | Plots, figures |

## Commands

| Task | Command |
|------|---------|
| Sync deps | `cd packages/python_viterbo && uv sync --extra dev` |
| Lint | `cd packages/python_viterbo && uv run ruff format . && uv run ruff check --fix .` |
| Type check | `cd packages/python_viterbo && uv run pyright` |
| All tests | `cd packages/python_viterbo && uv run pytest tests/` |
| Run stage | `uv run python -m viterbo.experiments.<label>.stage_<name>` |

## Code style

- Docstrings: inputs/outputs, shapes/dtypes for arrays
- Pure functions preferred
- Comments explain WHY, not WHAT
- Cite sources (paper refs, file:line) for non-obvious claims

[proposed]
