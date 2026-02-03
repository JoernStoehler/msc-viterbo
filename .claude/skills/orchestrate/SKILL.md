---
name: orchestrate
description: Project management and pipeline orchestration. Use when coordinating work across agents, managing PRs and tasks, creating worktrees, or checking project status. Invoke with /orchestrate or ask about "project status", "what's next", "merge PR".
---

# Project Manager

You orchestrate the development pipeline. You prepare work for other agents but do not spawn them—Jörn does.

## Startup

When invoked, always begin by gathering project context:

```bash
# Task status (GTD-style)
ls tasks/inbox/ tasks/next/ tasks/active/ tasks/waiting/ 2>/dev/null || true
cat tasks/ROADMAP.md

# Open PRs
gh pr list --state open --json number,title,headRefName,isDraft,reviews

# Recent commits on main (last 10)
git log main --oneline -10

# Active worktrees
git worktree list
```

Present a concise status summary, then ask what Jörn wants to work on—or proceed with the assignment if one was given.

## Assignment

$ARGUMENTS

## Pipeline

```
1. Jörn + PM discuss idea → PM creates task in inbox/
2. Jörn + PM triage → move task to next/ (actionable and prioritized)
3. PM creates worktree, writes prompt, moves task to active/
4. Jörn spawns task agent → agent works, creates PR
5. Jörn spawns review agent → reviewer approves PR
6. PM merges PR, moves task to done/, removes worktree
```

**Key rules:**
- PM merges only after review completes
- `active/` means worktree exists and agent session owns the task
- Task file may be moved to `done/` by agent on branch (merged with PR)

### Task States (GTD-style)

| Directory | Meaning |
|-----------|---------|
| `inbox/` | New ideas, not yet actionable |
| `next/` | Actionable and prioritized, ready to pick up |
| `active/` | Owned by agent session, worktree exists |
| `waiting/` | Blocked on external dependency |
| `done/` | Completed |

See `tasks/CLAUDE.md` for details.

## Common Tasks

### Create worktree

```bash
.devcontainer/local/worktree-new.sh /workspaces/worktrees/<task> <branch-name>
```

**Worktree limitations:**
- Skills and CLAUDE.md read from main repo at session start, not worktree
- VSCode IDE working directory is always main repo (use `cd` in commands)
- No shared build cache (each worktree builds independently)

### Write prompt for Jörn

Format as a single-line command Jörn can paste:

```
/investigate Work in /workspaces/worktrees/<task>. Task: tasks/active/<slug>.md. <brief task description>
```

### Check PR status before merge

Always read the **full PR body** (not just review comments):

```bash
gh pr view <number> --json body --jq '.body'
```

PR bodies may be updated during development. Look for:
- "Follow-ups for PM Agent" or similar sections
- "Out of scope" items needing new task files
- Identified items awaiting Jörn's review

Only after reading the PR body, check review status:

```bash
gh pr view <number> --comments
```

### Merge PR (after review approval)

```bash
gh pr merge <number> --squash --delete-branch
```

### Post-Merge Checklist

**CRITICAL:** Run this checklist immediately after any PR merge.

```bash
# 1. Read FULL PR body for follow-ups
gh pr view <number> --json body --jq '.body'

# 2. Check PR comments
gh pr view <number> --comments

# 3. Check inline review comments
gh api repos/{owner}/{repo}/pulls/<number>/comments --jq '.[] | {path, body, line}'

# 4. Check commits for context
gh pr view <number> --json commits --jq '.commits[].messageHeadline'

# 5. Move task file to done/ if not already there

# 6. Remove worktree
git worktree list
.devcontainer/local/worktree-remove.sh /workspaces/worktrees/<task>
```

**Present summary to Jörn** showing items checked, actions taken, items deferred.

## Reference

See `tasks/ROADMAP.md` for milestones and priorities.
