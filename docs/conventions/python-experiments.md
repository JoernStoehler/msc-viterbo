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
├── FINDINGS.md          # Interpretation of results + escalation procedures
├── stage_build.py       # Generate data
├── stage_analyze.py     # Compute results
└── stage_plot.py        # Create figures
```

Why stages: separate expensive computation (build) from cheap iteration (analyze/plot). Re-run analysis without regenerating data.

## Teaching Example

`src/viterbo/experiments/example_pipeline/` demonstrates all conventions. Study it first.

## Experiment Lifecycle

Experiments follow a standard agent workflow. Each phase has an owner who produces an output before handing off.

### Initial Development

| Phase | Owner | Output |
|-------|-------|--------|
| Ideation | Jörn / PM agent / any agent → PM agent | Idea discussed with PM |
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
| Maintenance | Any agent | Updated FINDINGS.md; escalate if experiment needs reopening (invalid results, mismatch between findings and artifacts) |

**Escalation triggers:**
- Validation tests that previously passed now fail
- Data artifacts contradict FINDINGS.md conclusions
- Upstream code changes invalidate assumptions in SPEC.md

When escalation is needed, open an issue referencing the experiment and describe what broke.

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

## FINDINGS.md Content

FINDINGS.md is a living document updated on each rerun:

- **Results summary**: Key findings from the data
- **Interpretation**: What the results mean for the research question
- **Escalation procedures**: When and how to flag issues (e.g., "if validation fails, open issue before updating thesis")
- **Changelog**: Dated entries when findings change significantly

## Philosophy

- **GitHub Issue tracks progress** - coordination, blockers, status updates
- **Files contain research content** - SPEC.md, FINDINGS.md, stages, data
- **Don't compress ideas** - preserve intellectual labor in SPEC/FINDINGS
- **Reproduction must be obvious** - pattern self-evident from repo structure
- **Escalate don't hide** - if results change qualitatively, flag it rather than silently updating

## Code Style

KISS, pure functions (closeness to math), fast dev cycle (no external users).
