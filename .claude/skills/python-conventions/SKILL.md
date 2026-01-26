---
name: python-conventions
description: Work on Python experiments in packages/python_viterbo. Use for layout conventions, stage entrypoints, lint/test commands, and asset/plot handling.
---

# Python Conventions (python_viterbo)

## CRITICAL: Read this skill before working on Python code

Agents MUST read this entire skill file before proposing or implementing Python code. Do not skip sections. Do not make up conventions that are not documented here.

## Terminology

- **label**: A short identifier for an experiment (e.g., `counterexample-hko`, `dimension-5-probing`). Used consistently across folder names, tracking table rows, and thesis section labels.
- **stage**: A discrete step in an experiment pipeline (e.g., `build`, `analyze`, `plot`).

## Directory layout

All paths relative to `packages/python_viterbo/`:

| Artifact | Path | Notes |
|----------|------|-------|
| Experiment code | `src/viterbo/experiments/<label>/` | One folder per experiment |
| Stage entrypoints | `src/viterbo/experiments/<label>/stage_<stage>.py` | CLI-invocable modules |
| Experiment spec | `src/viterbo/experiments/<label>/SPEC.md` | Research question, success criteria |
| Shared helpers | `src/viterbo/common/` | Avoid premature abstraction |
| Configs | `config/<label>/<variant>.json` | Parameters for reproducible runs |
| Data artifacts | `data/<label>/` | Outputs from experiments (Git LFS for large files) |
| Assets for thesis | `../latex_viterbo/assets/<label>/` | Plots, figures, tables |

## Commands

| Task | Command |
|------|---------|
| Lint | `scripts/lint.sh` (runs ruff format, ruff check --fix, pyright) |
| All tests | `uv run pytest tests/` |
| Targeted tests | `uv run pytest <path>` |

## Stage invocation

```bash
uv run python -m viterbo.experiments.<label>.stage_<stage> [--config config/<label>/<variant>.json]
```

## Code conventions

- Follow ML/data-science best practices.
- Docstrings: inputs/outputs, side effects, shapes/dtypes, contracts.
- Prefer pure functions.
- Comments explain WHY, not WHAT.
- Cite sources for non-obvious claims (paper refs, file paths, line numbers).

## Plots and assets

- Python generates layout/style; LaTeX only includes the result.
- Output to `packages/latex_viterbo/assets/<label>/`.
- Use descriptive filenames (e.g., `orbit-projection.png`, not `fig1.png`).

[proposed]
