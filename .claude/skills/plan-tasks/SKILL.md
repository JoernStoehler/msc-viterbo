---
name: plan-tasks
description: Creating and managing tasks in GitHub Issues. Use when Jörn requests task creation, when discovered work needs tracking. NOT for normal work logs (use issue comments).
---

# Task Management with GitHub Issues

## Overview

Work tracked in **GitHub Issues**, **Milestones**, and **Discussions**.

- Code work → GitHub Issues
- Experiment ideas → GitHub Discussions → Issue when ready
- Experiments have tracking issue + SPEC.md/FINDINGS.md in repo

## Creating Issues

Use `gh issue create` with templates:

```bash
# Bug report
gh issue create --template bug.yml --title "Volume returns negative for simplex"

# Feature request
gh issue create --template feature.yml --title "Remove FFI 10-facet limit"

# Experiment
gh issue create --template experiment.md --title "random-polytope-sys-distribution"
```

Or use web UI: templates at `.github/ISSUE_TEMPLATE/`

## Issue Structure

**Title:** Action-oriented, specific
- Good: "Fix negative volume for degenerate polytopes"
- Bad: "Volume bug"

**Description:** Problem, approach, acceptance criteria (template guides this)

**Labels:** Apply as needed
- Type: `bug`, `enhancement`, `experiment`, `documentation`
- Area: `rust`, `python`, `thesis`, `infra`
- `blocked` when waiting on dependencies

**Footer (REQUIRED):**
```markdown
---
*Agent: worktree-name*
```
Issues without footer = from Jörn.

## Work Logs

Use **issue comments** for chronological notes:

```bash
gh issue comment 123 --body "Tried approach X, failed because Y.

Found that module A depends on B unexpectedly. Need to refactor or work around.

---
*Agent: feat/fix-volume*"
```

Work logs should be:
- **High fidelity, low shame**: "Tried X, failed" is valuable
- **Chronological**: Each comment = progress update
- **Attributed**: Footer shows which agent/branch

## When to Add Tasks

Only when:
- Work discovered that can't be done now (blocked, out of scope)
- Jörn explicitly requests it

**Don't speculatively add tasks** - Jörn manages the backlog.

## Cross-Referencing

Use `#123` to reference issues:
```markdown
Blocked by: #45 (complete billiard section)
Blocks: #67 (algorithm comparison experiment)
See also: #89 (related PR)
```

## Closing Issues

When work complete:
```bash
gh issue close 123 --comment "Completed. Tests passing, docs updated.

---
*Agent: feat/fix-volume*"
```
