# Python Experiments

Structure, workflow, and conventions for thesis experiments in `packages/python_viterbo/`.

## File Layout

| Artifact | Location |
|----------|----------|
| Tracking | GitHub Issue (label: `experiment`) |
| Code | `src/viterbo/experiments/<label>/` |
| SPEC.md | `src/viterbo/experiments/<label>/SPEC.md` |
| FINDINGS.md | `src/viterbo/experiments/<label>/FINDINGS.md` |
| Configs | `config/<label>/` |
| Data | `data/<label>/` |
| Thesis assets | `packages/latex_viterbo/assets/<label>/` |

### Standard Code Structure

```
src/viterbo/experiments/<label>/
├── SPEC.md              # Research question, method, success criteria
├── FINDINGS.md          # Interpretation of results
├── stage_build.py       # Generate data
├── stage_analyze.py     # Compute results
└── stage_plot.py        # Create figures
```

Why stages: separate expensive computation (build) from cheap iteration (analyze/plot). Re-run analysis without regenerating data.

## Teaching Example

`src/viterbo/experiments/example_pipeline/` demonstrates all conventions. Study it first.

## Workflow Stages

### 1. Ideation

Create GitHub Discussion or propose in existing issue:
- Research question + motivation
- Rough approach
- How it connects to other work
- Dependencies/blockers

If agent-proposed, mark with `[proposed]` in discussion.

### 2. Specification

1. Create GitHub Issue: `gh issue create --template experiment.md --title "label" --label experiment`
2. Create experiment folder with SPEC.md

### 3. Execution

1. Implement stages
2. Run experiments, produce data
3. Write FINDINGS.md as living document (chronological insights, bugs found, what worked)
4. Add work logs to issue via comments

### 4. Polishing

Clean code, generate publication-quality figures, write thesis section.

## Running Stages

```bash
cd /workspaces/worktrees/<task>/packages/python_viterbo
uv run python -m viterbo.experiments.<label>.stage_build
uv run python -m viterbo.experiments.<label>.stage_analyze
uv run python -m viterbo.experiments.<label>.stage_plot
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

## Philosophy

- **GitHub Issue tracks progress** - coordination, blockers, status updates
- **Files contain research content** - SPEC.md, FINDINGS.md, stages, data
- **Don't compress ideas** - preserve intellectual labor in SPEC/FINDINGS
- **Reproduction must be obvious** - pattern self-evident from repo structure

## Code Style

KISS, pure functions (closeness to math), fast dev cycle (no external users).
