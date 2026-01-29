# Python Experiment Conventions

Structure and patterns for experiments in `packages/python_viterbo/`.

## Standard Layout

```
src/viterbo/experiments/<label>/
├── SPEC.md              # Research question, method, success criteria
├── FINDINGS.md          # Interpretation of results
├── stage_build.py       # Generate data
├── stage_analyze.py     # Compute results
└── stage_plot.py        # Create figures

config/<label>/
├── default.json         # Parameters
└── test.json            # Alternative configs

data/<label>/            # Output artifacts
tests/test_<label>.py    # Tests
```

## Teaching Example

`src/viterbo/experiments/example_pipeline/` demonstrates all conventions. Study it before creating new experiments.

## Running Stages

```bash
cd /workspaces/worktrees/<task>/packages/python_viterbo
uv run python -m viterbo.experiments.<label>.stage_build
uv run python -m viterbo.experiments.<label>.stage_analyze
uv run python -m viterbo.experiments.<label>.stage_plot
```

## Reproduction Must Be Obvious

Pattern should be self-evident from repo structure:

```bash
# Good
for cfg in config/polytope-families/*.json; do
  uv run python -m viterbo.experiments.polytope_families.stage_build "$cfg"
done
```

Bad: "Run with configs A, B, and C" (which configs? where?)

## Code Style

- **KISS**: Avoid clever tricks and premature abstractions
- **Pure functions**: Preferred when possible
- **Type annotations**: Use where helpful; `# type: ignore` for pyright false positives
- **Testing**: Sanity checks, fast dev cycle, use test configs with small data
