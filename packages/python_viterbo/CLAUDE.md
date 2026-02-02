# python_viterbo

[proposed]

Python experiments for thesis research.

## Structure

```
src/viterbo/experiments/<label>/
  SPEC.md           # Research question, method, success criteria
  FINDINGS.md       # Results, interpretation, escalation procedures
  stage_build.py    # Generate data (expensive)
  stage_analyze.py  # Compute results (cheap)
  stage_plot.py     # Create figures
```

Data and configs live outside the code:
- `config/<label>/` - Configuration files
- `data/<label>/` - Generated data
- `../latex_viterbo/assets/<label>/` - Thesis figures

## Commands

```bash
uv sync --extra dev                                    # Install dependencies
uv run pytest                                          # Run tests
uv run ruff check src tests                            # Lint
uv run python -m viterbo.experiments.<label>.stage_build
uv run python -m viterbo.experiments.<label>.stage_analyze
uv run python -m viterbo.experiments.<label>.stage_plot
```

## Teaching Example

Study `src/viterbo/experiments/example_pipeline/` first - it demonstrates all conventions.

## Experiment Lifecycle

See `docs/conventions/python-experiments.md` for the full workflow:
- PM agent creates issues, planner writes SPEC.md
- Developer implements stages and FINDINGS.md
- Reviewer approves PR

**Escalation triggers** (reopen issue):
- Validation tests that previously passed now fail
- Data artifacts contradict FINDINGS.md
- Upstream code changes invalidate SPEC.md assumptions

## Code Style

- KISS, pure functions
- Fast dev cycle (no external users)
- Stage separation: expensive build vs cheap analyze/plot iteration
