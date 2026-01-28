---
name: plan-tasks
description: Adding or reorganizing tasks in TODO.md. Use when Jörn requests task additions, when discovered work needs tracking, or when restructuring the task list. NOT for normal task completion (marking [x]).
---

# Task Planning

## TODO.md Structure

- **Checklist sections** at top for quick scanning
- **Details section** at bottom for items needing context
- **Status markers**: `[ ]` pending, `[x]` done, `[-]` blocked/deferred

## When to Add Tasks

Only when:
- Work is discovered that can't be done now (blocked, out of scope)
- Jörn explicitly requests it

**Don't speculatively add tasks** - Jörn manages the backlog.

## Simple vs Detailed Items

**Simple items:** One line in checklist
```markdown
- [ ] Fix FFI facet limit
```

**Items with context:** Add sub-bullets or `## label` section in Details
```markdown
## fix-ffi-facet-limit

Current FFI limits to 10 facets due to timeout concerns. Need to:
1. Profile HK2017 on 11-12 facet polytopes
2. Adjust timeout if performance acceptable
3. Update FFI validation
```

## How to Write Good Task Descriptions

- **Action-oriented**: "Fix X", "Implement Y", "Verify Z"
- **Include acceptance criteria** if not obvious
- **Reference related issues/experiments/code** locations
- **Note blockers explicitly** with `[-]` marker
