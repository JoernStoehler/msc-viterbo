# experiments/

[proposed]

Python experiment pipelines for empirical research.

## Structure

Each experiment is a folder with:
- `SPEC.md` — Research question, method, success criteria
- `stage_*.py` — Pipeline stages (build → analyze → plot)
- `test_*.py` — Colocated tests

See `_example/` for a working reference.

## Commands

```bash
cd experiments
uv run python <label>/stage_build.py   # Run a stage
uv run pytest <label>/                  # Run tests
uv run ruff check . && uv run ruff format .  # Lint
```

## Data Flow

- Outputs → `data/outputs/<label>/`
- Thesis figures → `thesis/assets/<label>/`

## Dependencies

Add to `pyproject.toml`, run `uv sync --extra dev`.

## See Also

- Skill `experiment-workflow` for creating new experiments or understanding the full lifecycle
