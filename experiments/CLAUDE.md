# experiments/CLAUDE.md

Python experiment pipelines for empirical research.

## Structure

```
experiments/
  __init__.py
  pyproject.toml     # Dependency management
  uv.lock
  conftest.py
  pytest.ini
  ruff.toml
  _example/          # Example experiment
    SPEC.md
    __init__.py
    stage_1.py
    test_stage_1.py
  <label>/           # One folder per experiment
  ...

data/                # Experiment pipeline outputs (sibling directory)
  _example/
    dataset.parquet
    analysis.csv
  <label>/
  ...

thesis/assets/       # Figures, .tex tables for thesis (sibling directory)
  _example/
    figure.png
  <label>/
  ...
```

## Commands

```bash
cd /workspaces/worktrees/<task>/experiments && ...
uv run python <label>/stage_build.py    # Run a stage
uv run pytest <label>/                  # Run tests
uv run ruff check . && uv run ruff format .  # Lint
```

## Data Flow

- Outputs → `data/<label>/`
- Thesis figures and tables → `thesis/assets/<label>/`

## Dependencies

Add to `pyproject.toml`, run `uv sync --extra dev`.

## See Also

- Skill `experiment-workflow` for creating new experiments or understanding the full lifecycle
