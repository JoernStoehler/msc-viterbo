---
name: experiment-workflow
description: How to create, run, and document Python experiments. SPEC.md, stage_*.py, FINDINGS.md lifecycle.
---

[proposed]

# Experiment Workflow

This skill covers the complete lifecycle of Python experiments in `experiments/`. Experiments are the primary way this thesis generates empirical evidence.

## File Layout

| Artifact | Location |
|----------|----------|
| Tracking | Task file in `tasks/` |
| Code | `experiments/<label>/` |
| SPEC.md | `experiments/<label>/SPEC.md` |
| Tests | `experiments/<label>/test_*.py` (colocated) |
| Data | `data/<label>/` |
| Thesis assets | `thesis/assets/<label>/` |

## Standard Code Structure

```
experiments/<label>/
├── SPEC.md              # Research question, method, success criteria
├── stage_build.py       # Generate data
├── test_stage_build.py  # Colocated test
├── stage_analyze.py     # Compute results
└── stage_plot.py        # Create figures
```

**Why stages?** Separate expensive computation (build) from cheap iteration (analyze/plot). Re-run analysis without regenerating data.

## Teaching Example

`experiments/_example/` demonstrates all conventions. Study it first when creating a new experiment.

## Experiment Lifecycle

### Initial Development

| Phase | Owner | Output |
|-------|-------|--------|
| Ideation | Jorn / PM agent / any agent -> PM agent | Idea discussed with PM |
| Issue creation | PM agent | GitHub issue with research question |
| Planning | Planner agent | SPEC.md with method and success criteria |
| Spec review | Spec-review agent | Approved SPEC.md (or back to planner) |
| Development | Developer agent | stage_* code, FINDINGS.md, artifacts, PR |
| Code review | Review agent | Approved PR (or escalate back) |
| Merge | PM agent | Merged PR, updated issues/milestones |

### Ongoing Maintenance

After initial development, experiments may be rerun when the codebase changes.

| Phase | Owner | Output |
|-------|-------|--------|
| Rerun | Any agent | Updated data and asset artifacts |
| Maintenance | Any agent | Updated FINDINGS.md; escalate if needed |

## Running Stages

```bash
cd experiments
uv run python <label>/stage_build.py
uv run python <label>/stage_analyze.py
uv run python <label>/stage_plot.py
```

## SPEC.md Template

```markdown
# <label> Experiment

**Status:** Ideation / Specified / In Progress / Complete

## Research Question
What are we trying to learn?

## Method
How will we answer the question?

## Success Criteria
What outcome means "we are satisfied"?

## Expected Outputs
- data/<label>/...
- assets/<label>/...
```

## FINDINGS.md Template

```markdown
# <label> Findings

## Results Summary
Key findings from the data.

## Interpretation
What the results mean for the research question.

## Escalation Procedures
When and how to flag issues.

## Changelog
- YYYY-MM-DD: Initial findings
- YYYY-MM-DD: Updated after <change>
```

## FINDINGS.md Content Guidelines

FINDINGS.md is a living document updated on each rerun:

- **Results summary**: Key findings from the data
- **Interpretation**: What the results mean for the research question
- **Escalation procedures**: When and how to flag issues (e.g., "if validation fails, open issue before updating thesis")
- **Changelog**: Dated entries when findings change significantly

## Stage Patterns

### stage_build.py

```python
"""Generate data for <label> experiment."""

from pathlib import Path

# All config hardcoded for reproducibility
CONFIG = {
    "experiment_name": "<label>",
    "variant": "full",  # Change to "smoke" for quick runs
}

DATA_DIR = Path(__file__).parent.parent.parent / "data" / "outputs" / CONFIG["experiment_name"]

def main():
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    # Generate data
    # Save to DATA_DIR / "results.json" or similar

if __name__ == "__main__":
    main()
```

### stage_plot.py

```python
"""Generate plots for <label> experiment."""

from pathlib import Path
import matplotlib.pyplot as plt

CONFIG = {"experiment_name": "<label>"}

DATA_DIR = Path(__file__).parent.parent.parent / "data" / "outputs" / CONFIG["experiment_name"]
ASSETS_DIR = Path(__file__).parent.parent.parent / "thesis" / "assets" / CONFIG["experiment_name"]

def main():
    ASSETS_DIR.mkdir(parents=True, exist_ok=True)
    # Load data
    # Create figures
    plt.savefig(ASSETS_DIR / "figure.pdf")

if __name__ == "__main__":
    main()
```

## Escalation Triggers

Escalate (open an issue referencing the experiment) when:

- Validation tests that previously passed now fail
- Data artifacts contradict FINDINGS.md conclusions
- Upstream code changes invalidate assumptions in SPEC.md

## Philosophy

- **Task files track progress** - coordination, blockers, status updates
- **Files contain research content** - SPEC.md, FINDINGS.md, stages, data
- **Don't compress ideas** - preserve intellectual labor in SPEC/FINDINGS
- **Reproduction must be obvious** - pattern self-evident from repo structure
- **Escalate don't hide** - if results change qualitatively, flag it rather than silently updating

## Code Style

- KISS (Keep It Simple)
- Pure functions (closeness to math)
- Fast dev cycle (no external users)

## Source

Extracted from deleted `docs/conventions/python-experiments.md`.
