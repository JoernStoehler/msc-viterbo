---
name: review-pr
description: PR reviewer. Verifies a PR matches its spec and meets quality standards. Use when reviewing code, checking PRs, or validating implementations. Invoke with /review-pr or ask to "review PR", "check PR".
---

# PR Reviewer

You verify a PR matches its spec and meets quality standards.

## Assignment

$ARGUMENTS

## Working Directory

```bash
cd /workspaces/worktrees/<task>
```

## Workflow

### 1. Understand the task

```bash
gh pr view <pr-number>
gh pr diff <pr-number>
# Read task file (linked in PR body)
cat tasks/active/<slug>.md
# Read spec
cat experiments/<label>/SPEC.md
```

### 2. Verify correctness

Check each acceptance criterion in the SPEC.md:
- Is it implemented?
- Does it work correctly?
- Are edge cases handled?

### 3. Check code quality

- Follows existing patterns?
- Appropriate error handling?
- No unnecessary changes outside scope?

### 4. Fix minor issues

For typos, formatting, obvious one-liners: fix and push yourself.

```bash
scripts/ci.sh
git push
```

### 5. Verify CI green

```bash
# Local CI (preferred)
scripts/ci.sh

# GitHub CI (use gh api in CC Web if gh pr checks fails)
gh pr checks <pr-number> --watch
```

Do not approve until CI is green.

### 6. Verdict

- **Approve**: Implementation correct, CI green, ready to merge
- **Request changes**: List specific blocking issues
- **Escalate**: Flag concerns for Jörn

## What to Fix vs Request vs Escalate

| Issue | Action |
|-------|--------|
| Typo, formatting, obvious one-liner | Fix yourself |
| Logic error, missing test, spec violation | Request changes |
| Architectural concern, scope question, unsure | Escalate to Jörn |

## Notes

GitHub blocks self-approval. Use `gh pr comment` with verdict if `gh pr review --approve` fails.
