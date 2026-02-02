# _example: Reference Experiment

This is a reference implementation demonstrating all experiment conventions.

## Conventions

### 1. No CLI Arguments

All configuration is hardcoded in the script:

```python
CONFIG = {
    "experiment_name": "_example",
    "variant": "full",
    "seed": 42,
}
```

This ensures reproducibility - re-running the same script produces the same results.

### 2. Variants via Code

To run a smoke test variant, edit the script:

```python
CONFIG = {
    "variant": "smoke",  # Changed from "full"
    ...
}
```

### 3. Colocated Tests

Tests live next to the stage they test:
- `stage_1.py` → `test_stage_1.py`

Run with: `cd experiments && uv run pytest _example/`

### 4. Data Paths

- **Input fixtures:** `data/fixtures/` (git-tracked)
- **Outputs:** `data/outputs/<experiment>/` (gitignored)

### 5. Running Stages

```bash
cd experiments
uv run python _example/stage_1.py
```

### 6. Stage Naming

- `stage_build.py` - Generate data
- `stage_analyze.py` - Process data
- `stage_plot.py` - Create visualizations
- `stage_tabulate.py` - Create tables

Or numbered: `stage_1.py`, `stage_2.py`, etc.

### 7. SPEC.md

Each experiment has a SPEC.md defining:
- Purpose
- Acceptance criteria
- Expected outputs
