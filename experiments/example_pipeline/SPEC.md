# example-pipeline Experiment

**Purpose:** Teaching example demonstrating all experiment conventions.

This is NOT a real experiment. It exists to show future agents what a complete
experiment looks like. Study this before creating new experiments.

## What This Demonstrates

1. **SPEC.md** — This file. Research question, method, success criteria.
2. **Config** — `config/example-pipeline/default.json` for parameterized runs.
3. **Multiple stages** — `stage_build.py`, `stage_analyze.py`, `stage_plot.py`.
4. **Data output** — `data/example-pipeline/results.json`.
5. **Tests** — `tests/test_example_pipeline.py`.
6. **Thesis assets** — Would go to `latex_viterbo/assets/example-pipeline/`.

## Research Question (Fake)

"Does the sum of squares grow quadratically with input size?"

## Method

1. **Build**: Generate synthetic data (list of random numbers).
2. **Analyze**: Compute sum of squares for various input sizes.
3. **Plot**: Visualize growth curve.

## Success Criteria

- All stages run without error.
- Tests pass.
- Output files are created in correct locations.

## Expected Outputs

- `data/example-pipeline/results.json` — Analysis results.
- `latex_viterbo/assets/example-pipeline/growth-curve.png` — Plot (if polishing).
