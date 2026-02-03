# tasks/

[proposed]

Local task tracking (GTD-style). Use instead of GitHub issues.

## Directories

| Directory | Meaning |
|-----------|---------|
| `inbox/` | New, uncategorized |
| `next/` | Actively working on |
| `waiting/` | Blocked on dependency |
| `review/` | Agent done, awaiting Jörn review |
| `done/` | Jörn approved |
| `blocked/` | Known blockers, parked |

Move files between directories to change status.

## Task File Format

```markdown
# <Task Title>

**Status:** <current directory>
**Priority:** P1/P2/P3
**Blocked by:** <if applicable>

## Goal
What needs to be done.

## Notes
Per-task context, plans, discoveries.
```

## See Also

- `ROADMAP.md` for milestones and priorities
- Skill `orchestrate` for the full PM workflow
