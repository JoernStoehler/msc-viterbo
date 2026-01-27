---
name: project-management
description: Add, update, or reorganize tasks in TODO.md or experiments.md. Most agents don't need this — they just complete assigned work.
---

# Project Management

[proposed]

## Files

| File | Purpose |
|------|---------|
| `TODO.md` (repo root) | Non-research tasks: implementation, writing, tooling, deferred bugs |
| `packages/latex_viterbo/experiments.md` | Research experiments with rich context |

## When to use which

- **Research experiments** (need hypothesis, approach, analysis plan) → experiments.md
- **Everything else** (implementation, bugs, writing, chores) → TODO.md

## TODO.md structure

```markdown
## Section Name (milestone or category)
- [ ] Task description
  - Optional: blocker, link to spec, brief context
- [ ] Simple task with no extra info
```

- Simple items: one line, checkbox, description
- Items with context: sub-bullets for blockers, links, notes
- Items needing rich detail: link to experiments.md or a spec file instead

## Most agents don't modify these files

Typical flow: agent receives task → completes it → marks done in TODO.md → hands off.

Only add new tasks when:
- Work is discovered that can't be done now (blocked, out of scope)
- Project owner requests it

Don't speculatively add tasks. Jörn manages the backlog.
