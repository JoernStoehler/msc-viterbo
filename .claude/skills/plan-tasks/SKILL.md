---
name: plan-tasks
description: How to properly add and flesh out tasks in TODO.md. Most agents just mark tasks done; use this skill when creating or reorganizing tasks.
---

# Task Planning

**When to use this skill:**
- You need to add new tasks to TODO.md (because work is discovered that can't be done now)
- You need to restructure or reorganize TODO.md for clarity
- Jörn explicitly asks you to add tasks

**When NOT to use this skill:**
- Just marking tasks `[x]` as done (that's in CLAUDE.md Agent Protocol, always-on)
- Normal thesis work (build, test, commit)

---

## TODO

This skill needs to be fleshed out with actual content about how to structure tasks.

Key topics to cover:
- TODO.md file structure (checklist sections vs details sections)
- Status markers (`[ ]`, `[x]`, `[-]`)
- When to add simple one-liners vs detailed sections
- How to write good task descriptions
- When to add tasks vs when to just do the work

**Current guidance (from project-management skill):**

### File Structure

`TODO.md` at repo root:
- **Checklist sections** at top for quick scanning
- **Details section** at bottom for items needing context

### Status Markers

- `[ ]` — pending
- `[x]` — done
- `[-]` — blocked or deferred (with note)

### Adding Items

**Simple items:** One line in the appropriate checklist section.
```markdown
- [ ] Fix FFI facet limit
```

**Items with context:** Add sub-bullets or a `## label` section in Details.

### When to Add Tasks

Only add new tasks when:
- Work is discovered that can't be done now (blocked, out of scope)
- Jörn requests it

**Don't speculatively add tasks.** Jörn manages the backlog.
