---
name: project-management
description: Conventions for TODO.md structure. All agents mark tasks done per CLAUDE.md Agent Protocol; this skill covers adding/reorganizing tasks.
---

# Project Management

**Essential:** All agents must mark tasks `[x]` when done — see CLAUDE.md Agent Protocol.

This skill covers TODO.md conventions for agents who need to add or reorganize tasks.

## File Structure

`TODO.md` at repo root:
- **Checklist sections** at top for quick scanning
- **Details section** at bottom for items needing context

## Status Markers

- `[ ]` — pending
- `[x]` — done
- `[-]` — blocked or deferred (with note)

## Adding Items

**Simple items:** One line in the appropriate checklist section.
```markdown
- [ ] Fix FFI facet limit
```

**Items with context:** Add sub-bullets or a `## label` section in Details.

## When to Add Tasks

Only add new tasks when:
- Work is discovered that can't be done now (blocked, out of scope)
- Jörn requests it

Don't speculatively add tasks. Jörn manages the backlog.
