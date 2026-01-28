---
name: plan-experiments
description: Planning or executing thesis experiments. Covers the lifecycle from ideation through polishing, tracking table, SPEC.md format, stage structure.
---

# Experiment Workflow

## Philosophy

**TODO.md tracks experiments** alongside other tasks. The "Research Experiments" section in the checklist area provides a quick scan; the "Details" section at the bottom preserves full context. [proposed]

**The checklist is an index; the detailed sections are the documentation.** Each experiment should have a `## <label>` section in the Details area that contains the actual content:
- The research question and any sub-questions it breaks into
- How this experiment connects to other experiments (dependencies, shared data, sequential logic)
- What the outcome implies for next steps (e.g., "if sys > 1 is rare, we need targeted search methods")
- Open questions and blockers
- Where the idea came from (conversation, paper, advisor discussion)

**Don't compress ideas.** When capturing a research idea, preserve the intellectual labor that went into articulating it. A one-line note in the table loses the nuance, connections, and decision points. Write the detailed section.

**One experiment can have multiple variants.** If an experiment explores multiple families or parameter settings (e.g., comparing "convex hull of random points" vs "intersection of random halfplanes"), keep it as one experiment entry. Each variant gets its own config file in `config/<label>/` (e.g., `convex-hull.json`, `halfplane-intersection.json`). The set of commands to run **for full reproduction** must be **obvious from the repo state** — no mental recall or documentation lookup required (e.g., "run for each config file in the directory"). Local iteration (one stage, one config) may use CLI args. Don't create separate table rows for each variant.

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
| Tracking | `TODO.md` (checklist + Details section) [proposed] |
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

### Ideation [proposed]

1. Add a checklist item to the "Research Experiments" section in `TODO.md` with: label, blocked status, brief note.
2. Add a `## <label>` section in the Details area at the bottom of TODO.md. This section should include:
   - The research question, stated clearly, plus any sub-questions
   - Proposed approach or methods
   - What patterns or answers you're looking for
   - How this experiment connects to others (dependencies, what it enables)
   - Blockers and dependencies
   - Where the idea came from (conversation, paper, advisor)
3. If agent-created, mark the section with `[proposed]`. No code folder yet at this stage.

### Specification

Create experiment folder with SPEC.md. Update tracking table to "Specified".

### Execution

Implement stages, run, produce data. See `develop-python` skill for code structure.

### Polishing

Clean up code, generate publication-quality figures, write thesis section.

## Approval Markers

Use `[proposed]` for agent-proposed content. Only Jörn removes these markers.
Ambiguous responses ("sounds fine") do not count as approval.

## Handoff [proposed]

When finishing work:
1. Update TODO.md (checklist status + Details section if needed)
2. Ensure SPEC.md reflects current state
3. Commit with message referencing label
