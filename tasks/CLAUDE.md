# tasks/CLAUDE.md

Local task tracking (GTD-style). Use instead of GitHub issues.

## Structure

```
tasks/
  ROADMAP.md       # Milestones, priorities, cross-cutting notes
  inbox/           # New, uncategorized tasks, idea drafts
  next/            # Actively worked on, usually there's a worktree & claude code session active in the background
  waiting/         # Blocked on scheduled dependency (e.g. another task in `next/`)
  blocked/         # Blocked on known but unscheduled dependency (e.g. another task in `inbox/`, some goal not even tracked as tasks yet)
  review/          # Intermediate done state, awaiting review from Jörn, usually there's a PR open
  done/            # Jörn gave approval, task merged or otherwise completed and archived
```

Move files between directories to change task status.
Typical sequence: `inbox` → `next` → `review` → `done`

## Task File Format

No strict format. Simple example:

```markdown
# <Task Title>

**Status:** <current directory>
**Priority:** P1/P2/P3
**Blocked by:** <if applicable>

## Goal
What needs to be done.

## Notes
Per-task context, plans, discoveries, clarifications.
```

## See Also

- Skill `orchestrate` for a full project management workflow
