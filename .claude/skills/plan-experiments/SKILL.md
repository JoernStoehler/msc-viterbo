---
name: plan-experiments
description: Planning or executing thesis research experiments. Use when designing experiments, writing SPEC.md files, organizing experiment stages, or tracking experiment progress.
---

# Experiment Workflow

## Philosophy

- **GitHub Issue tracks progress** - coordination, blockers, status updates
- **Files in repo contain research content** - SPEC.md, FINDINGS.md, stages, data
- **Don't compress ideas** - preserve intellectual labor in SPEC.md and FINDINGS.md
- **One experiment, multiple variants** - use separate config files when you know how to abstract
- **Multiple experiments, abstract later** - duplicate first, refactor if overlap persists
- **Reproduction must be obvious** - pattern self-evident from repo structure

## Study Before Creating

Always study `src/viterbo/experiments/example_pipeline/` first - complete teaching example with all conventions.

## Terminology

- **label**: Short identifier (e.g., `random-polytope-sys-distribution`), used consistently

## Workflow Stages

1. **Ideation** - Discussion or proposal to clarify research question
2. **Specification** - Create issue + SPEC.md with success criteria
3. **Execution** - Implement stages, run, write FINDINGS.md
4. **Polishing** - Clean code, publication figures, thesis section

Stages overlap - iterate as you learn.

## File Locations

| Artifact | Location |
|----------|----------|
| Tracking | GitHub Issue (label: `experiment`) |
| Code | `packages/python_viterbo/src/viterbo/experiments/<label>/` |
| SPEC.md | `packages/python_viterbo/src/viterbo/experiments/<label>/SPEC.md` |
| FINDINGS.md | `packages/python_viterbo/src/viterbo/experiments/<label>/FINDINGS.md` |
| Configs | `packages/python_viterbo/config/<label>/` |
| Data | `packages/python_viterbo/data/<label>/` |
| Thesis assets | `packages/latex_viterbo/assets/<label>/` |

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

## Ideation Stage

Create **GitHub Discussion** or propose in existing issue/conversation:
- Research question + motivation
- Rough approach
- How it connects to other work
- Dependencies/blockers

If agent-proposed, mark with `[proposed]` in discussion.

## Specification Stage

1. Create **GitHub Issue** using experiment template:
   ```bash
   gh issue create --template experiment.md --title "label" --label experiment
   ```
2. Create experiment folder with SPEC.md:
   ```
   packages/python_viterbo/src/viterbo/experiments/<label>/
     SPEC.md
     __init__.py
   ```
3. Add footer to issue:
   ```markdown
   ---
   *Agent: worktree-name*
   ```

## Execution Stage

1. Implement stages (see develop-python skill for code structure)
2. Run experiments, produce data
3. **Write FINDINGS.md** as living document:
   - Update chronologically as insights emerge
   - Document bugs found, approaches tried, what worked/didn't
   - Include tables, equations, observations
   - No need for footer (versioned with code)
4. Add **work log to issue** via comments:
   ```bash
   gh issue comment N --body "Stage 1 complete. Discovered X. Next: Y.

   ---
   *Agent: worktree-name*"
   ```

## Polishing Stage

Clean up code, generate publication-quality figures, write thesis section.

## Handoff

When finishing work:
1. Update SPEC.md status
2. Ensure FINDINGS.md is complete
3. Close or update issue with final status
4. Ensure thesis assets ready
5. Commit with message referencing label

## Key Difference from Code Tasks

- **Issue** = tracking, coordination, work log (with footers)
- **SPEC.md + FINDINGS.md** = research content (versioned, no footers)
- FINDINGS.md is chronological, honest, detailed (similar to issue comments but richer format)
