---
name: experiment-workflow
description: Planning or executing thesis experiments. Covers the lifecycle from ideation through polishing, tracking table, SPEC.md format, stage structure.
---

# Experiment Workflow

## Philosophy

**experiments.md is a living document**, not a rigid specification. It captures ideas at various stages of development. The format can evolve as needs change.

**The table is an index, not the documentation.** Each experiment should have a detailed `## section` below the table that preserves:
- Full reasoning and sub-questions
- Connections to other experiments
- Strategic implications ("if X then Y")
- Open questions and blockers
- Context from conversations, papers, advisor discussions

**Don't compress ideas.** When capturing a research idea, preserve the intellectual labor that went into articulating it. A one-line note in the table loses the nuance, connections, and decision points. Write the detailed section.

**One experiment can have multiple variants.** If an experiment explores multiple families/parameters (e.g., "convex hull of random points" vs "intersection of random halfplanes"), that's one experiment with variants as parameters — not separate experiment entries. Don't spam the table with many near-duplicate rows.

**Ideas have broader context.** An experiment idea doesn't exist only in experiments.md. It connects to:
- Conversations where the idea emerged
- Thesis chapters it might inform
- GitHub issues and roadmap
- Algorithm development (what's computable)
- Prior work (papers, theses)
- Follow-up questions that will emerge from results

## Example: example-pipeline

Study `src/viterbo/experiments/example_pipeline/` for a complete teaching example:
- SPEC.md with research question, method, success criteria
- Multiple stages: `stage_build.py` → `stage_analyze.py` → `stage_plot.py`
- Config file at `config/example-pipeline/default.json`
- Tests at `tests/test_example_pipeline.py`

## Terminology

- **label**: Short identifier (e.g., `polytope-database`). Used consistently in folder names, tracking table, config, data, assets.

## Workflow Stages

1. **Ideation** — Turn vague idea into clear research question
2. **Specification** — Write SPEC.md with success criteria
3. **Execution** — Implement and run
4. **Polishing** — Clean up for thesis publication

## Where Things Live

| Artifact | Location |
|----------|----------|
| Tracking table | `packages/latex_viterbo/experiments.md` |
| Experiment code | `packages/python_viterbo/src/viterbo/experiments/<label>/` |
| SPEC.md | `packages/python_viterbo/src/viterbo/experiments/<label>/SPEC.md` |
| Configs | `packages/python_viterbo/config/<label>/` |
| Data | `packages/python_viterbo/data/<label>/` |
| Thesis assets | `packages/latex_viterbo/assets/<label>/` |
| Polished writeups | `packages/latex_viterbo/chapters/appendix-detailed-experiments.tex` |

## SPEC.md Template

```markdown
# <label> Experiment

**Status:** Ideation / Specified / In Progress / Complete

## Research Question

What are we trying to learn?

## Method

How will we answer the question?

## Success Criteria

What outcome means "it worked"?

## Expected Outputs

- data/<label>/...
- assets/<label>/...
```

## Stage Details

### Ideation

1. Add row to tracking table (`experiments.md`) with label, status, brief research question, notes
2. Add detailed `## <label>` section below the table with full reasoning:
   - Research question and sub-questions
   - Proposed approach/methods
   - What patterns or answers we're looking for
   - Connections to other experiments
   - Blockers and dependencies
   - Context (where the idea came from, related prior work)
3. Mark `[proposed]` if agent-created. No code folder yet.

### Specification

Create experiment folder with SPEC.md. Update tracking table to "Specified".

### Execution

Implement stages, run, produce data. See `python-conventions` skill for code structure.

### Polishing

Clean up code, generate publication-quality figures, write thesis section.

## Approval Markers

Use `[proposed]` for agent-proposed content. Only Jörn removes these markers.
Ambiguous responses ("sounds fine") do not count as approval.

## Handoff

When finishing work:
1. Update tracking table
2. Ensure SPEC.md reflects current state
3. Commit with message referencing label
