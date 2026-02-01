# GitHub Issues & Task Management

Work tracking conventions using GitHub Issues and Milestones.

## Overview

- Code work → GitHub Issues
- Experiments have tracking issue + SPEC.md/FINDINGS.md in repo

## Creating Issues

```bash
# Bug report
gh issue create --template bug.yml --title "Volume returns negative for simplex"

# Feature request
gh issue create --template feature.yml --title "Remove FFI 10-facet limit"

# Experiment
gh issue create --template experiment.md --title "random-polytope-sys-distribution"
```

Templates at `.github/ISSUE_TEMPLATE/`

## Issue Structure

**Title:** Action-oriented, specific
- Good: "Fix negative volume for degenerate polytopes"
- Bad: "Volume bug"

**Description:** Problem, approach, acceptance criteria (template guides this)

**Labels:**
- Type: `bug`, `enhancement`, `experiment`, `documentation`
- Area: `rust`, `python`, `thesis`, `infra`
- `blocked` when waiting on dependencies

**Footer (REQUIRED for agent-created issues):**
```markdown
---
*Agent: worktree-name*
```
Issues without footer = from Jörn.

## Work Logs

Use issue comments for chronological progress notes:

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

## When to Create Issues

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

```bash
gh issue close 123 --comment "Completed. Tests passing, docs updated.

---
*Agent: feat/fix-volume*"
```
