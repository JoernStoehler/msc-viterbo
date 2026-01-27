---
name: project-management
description: Add, update, or reorganize tasks in TODO.md. Most agents don't need this — they just complete assigned work.
---

# Project Management

[proposed]

## File

All task tracking lives in `TODO.md` at repo root:
- **Checklist sections** at top for quick scanning (Algorithm Toolbox, Thesis Writing, Research Experiments, etc.)
- **Details section** at bottom for items needing context

## Status markers

- `[ ]` — pending
- `[x]` — done
- `[-]` — blocked or deferred (with note)

## Writing quality

Every entry must be:
- **Actionable** — clear what "done" means
- **Unambiguous** — no jargon without definition
- **Relevant** — only information needed to act on the task
- **Scannable** — one concept per line; details go in sub-bullets or Details section

## Adding items

**Simple items:** One line in the appropriate checklist section.
```markdown
- [ ] Fix FFI facet limit
```

**Items with brief context:** Add sub-bullets.
```markdown
- [-] FFI ergonomics (#37) — deferred, not blocking core work
```

**Items needing rich detail:** Add a `## label` section in the Details area at the bottom.

## Most agents don't modify TODO.md

Typical flow: agent receives task → completes it → marks done → hands off.

Only add new tasks when:
- Work is discovered that can't be done now (blocked, out of scope)
- Project owner requests it

Don't speculatively add tasks. Jörn manages the backlog.
