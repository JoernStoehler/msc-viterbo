---
name: skill-conventions
description: Conventions for writing and maintaining skills in this project. Use when creating, reviewing, or refactoring skills. Defines structure (invariant vs workflow sections), naming, and anti-patterns.
---

# Skill Conventions

Project-specific conventions for skills. See also `skill-creator` for general skill creation guidance.

## Structure

Skills contain two types of content, clearly separated:

### Invariant Sections
What's true about the repo/domain. Use descriptive noun headers.

```markdown
## File Layout
## Lifecycle States
## Algorithm Selection
```

Content: folder structures, file layouts, states, constraints, expectations, domain knowledge.

### Workflow Sections
How to do something. Use verb headers.

```markdown
## Workflow
## Create PR
## Run Analysis
```

Content: sequential steps, commands, decision trees.

### Mixed Skills
Topical skills may contain both. Separate clearly:

```markdown
# Experiments

## File Layout          ← invariant
...

## Lifecycle States     ← invariant
...

## Create Experiment    ← workflow
...

## Run Analysis         ← workflow
...
```

## Naming

| Type | Name style | Examples |
|------|------------|----------|
| Workflow-focused | verb | `implement`, `review-pr`, `troubleshoot` |
| Invariant-focused | noun | `capacity-algorithms`, `cc-web-workarounds` |
| Mixed/topical | topic + `-workflow` if needed | `experiment-workflow`, `proof-first-workflow` |

## Anti-Patterns

1. **Speculative content** — Don't write workflows not based on real usage
2. **Drift** — Delete or update content that no longer matches reality
3. **Unclear sections** — Always label sections so readers know invariant vs workflow
4. **Redundancy** — Don't duplicate CLAUDE.md content; reference it
5. **Over-broadcasting** — Put invariants in CLAUDE.md if they apply to all agents in a directory

## Refactor Checklist

When reviewing/refactoring a skill:

- [ ] Sections clearly labeled (invariant vs workflow obvious from header)
- [ ] No speculative workflows (all based on real usage)
- [ ] Content matches current reality
- [ ] Naming follows convention (verb/noun appropriate)
- [ ] No redundancy with CLAUDE.md files
- [ ] Anti-patterns addressed
