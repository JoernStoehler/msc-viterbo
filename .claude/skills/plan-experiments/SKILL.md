---
name: plan-experiments
description: Planning or executing thesis research experiments. Use when designing experiments, writing SPEC.md files, organizing experiment stages, or tracking experiment progress.
---

# Experiment Workflow

## Philosophy

- **TODO.md tracks experiments** alongside other tasks
- **Checklist is index; Details sections are documentation**
- **Don't compress ideas** - preserve intellectual labor when capturing research ideas
- **One experiment, multiple variants** - use separate config files, not separate experiment entries, when you already know how to abstract
- **Multiple experiments, abstract later** - if experiments have overlap but are different in lifecycle or purpose, just copy/duplicate in order to have modules that can be changed independently. later, if the overlap remains, you can always refactor and abstract and merge.
- **Reproduction must be obvious** - pattern should be self-evident from repo structure

## Study Before Creating

Always study `src/viterbo/experiments/example_pipeline/` first - it's a complete teaching example with all conventions (SPEC.md, multiple stages, config files, tests).

## Terminology

- **label**: Short identifier (e.g., `polytope-database`), used consistently across folders

## Workflow Stages

1. **Ideation** - Turn vague idea into clear research question
2. **Specification** - Write SPEC.md with success criteria
3. **Execution** - Implement and run and interpret
4. **Polishing** - Clean up for thesis publication

Of course stages are not strictly separated, agents can move back and forth as they learn more about the problem.

## File Locations

| Artifact | Location |
|----------|----------|
| Tracking | TODO.md (checklist + Details section) |
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

1. Add checklist item to "Research Experiments" section in TODO.md with: label, blocked status, brief note
2. Add `## <label>` section in Details area at bottom of TODO.md. Include:
   - Research question (clearly stated) + sub-questions
   - Proposed approach or methods
   - What patterns you're looking for
   - How this connects to other experiments (dependencies, what it enables)
   - Blockers and dependencies
   - Where the idea came from (conversation, paper, advisor)
3. If agent-created, mark section with `[proposed]`. No code folder yet at this stage.

## Specification Stage

Create experiment folder with SPEC.md. Update TODO.md tracking to "Specified".

## Execution Stage

Implement stages, run, produce data. See develop-python skill for code structure.
Analyze results, write FINDINGS.md with observations, interpretations and learnings.

## Polishing Stage

Clean up code, generate publication-quality figures, write thesis section.

## Handoff

When finishing work:
1. Update TODO.md (checklist status + Details section if needed)
2. Ensure SPEC.md reflects current state
3. Ensure FINDINGS.md records interpretations
4. Ensure thesis assets and text pass style review
5. Commit with message referencing label
