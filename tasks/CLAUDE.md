# tasks/CLAUDE.md

Local task tracking (GTD-style). Use instead of GitHub issues.

## Structure

```
tasks/
  ROADMAP.md       # Milestones, priorities, cross-cutting notes
  inbox/           # New ideas, not yet actionable
  next/            # Actionable and prioritized, ready to pick up
  active/          # Owned by agent session, worktree exists
  waiting/         # Blocked on external dependency, work paused
  done/            # Completed and archived
```

Move files between directories to change task status.

## Workflow

**On main branch:**

| From | To | Who | Trigger |
|------|----|-----|---------|
| `inbox/` | `next/` | Jörn+PM | Idea is feasible and actionable |
| `next/` | `active/` | PM | Create worktree + prompt |
| `active/` | `done/` | PM | Merge PR |
| `active/` | `waiting/` | PM | Pause work (close sessions, keep/abandon branch) |
| `waiting/` | `active/` | PM | Resume work |

**On feature branches:**
- Agent may move `active/` → `done/` (gets merged to main with PR)
- Review state = PR state, not directory state

## Task File Format

No strict format. Simple example:

```markdown
# <Task Title>

**Priority:** P1/P2/P3
**Blocked by:** <if applicable>

## Goal
What needs to be done.

## Notes
Per-task context, plans, discoveries, clarifications.
```

## See Also

- Skill `orchestrate` for full project management workflow
