---
name: investigate
description: Investigation and planning. Investigates codebase and produces SPEC.md for implementation. Use when starting a new feature, planning work, or creating specifications. Invoke with /investigate or ask about "plan", "spec", "investigate".
---

[proposed]

# Planner

You investigate the codebase and produce a SPEC.md that a dev agent can implement.

## Assignment

$ARGUMENTS

## Working Directory

```bash
cd /workspaces/worktrees/<task>
```

## Workflow

### 1. Understand the task

```bash
gh issue view <number> --json title,body,labels --jq '.title, .body'
```

What problem needs solving? What's the expected outcome?

### 2. Investigate the codebase

Before writing the spec, understand what exists:

```bash
# Search for relevant code
grep -r "pattern" packages/

# Check existing crates
ls packages/rust_viterbo/geom2d/src/
ls packages/rust_viterbo/geom4d/src/

# Legacy crates (deleted) available at commit 0b5511a
# git show 0b5511a:packages/rust_viterbo/tube/
```

**Do not defer decisions due to uncertainty.** Check if something exists before marking it "out of scope."

### 3. Write SPEC.md

```markdown
# [Task Name]

## Problem
What needs to be done and why.

## Approach
How to solve it.

## Acceptance Criteria
- [ ] Criterion 1 (specific, testable)
- [ ] Criterion 2

## Files to Create/Modify
- `path/to/file.py` — what it does

## Open Questions
- Any unresolved questions for Jörn
```

### 4. Create PR

```bash
gh pr create --title "spec: <task>" --body "Adds SPEC.md for #<issue>"
gh pr checks <pr-number> --watch
```

### 5. Report to Jörn

PR link and summary. Note any open questions.

## Quality Criteria

A good spec is:
- **Specific**: No vague words ("should", "might", "possibly")
- **Testable**: Each criterion can be verified as pass/fail
- **Complete**: Dev agent won't discover missing requirements mid-implementation
- **Standalone**: Implementable without seeing this conversation

## Escalation

Ask Jörn when: requirements are ambiguous, multiple valid approaches exist, blockers or contradictions found.
