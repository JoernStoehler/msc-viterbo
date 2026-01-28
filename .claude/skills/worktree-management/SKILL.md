---
name: worktree-management
description: Manage git worktrees for this repo. Local uses scripts, Codespaces use manual git commands.
---

# Worktree Management

## Environment-Dependent

| Environment | Worktree Method |
|-------------|-----------------|
| Local | Scripts (`.devcontainer/local/worktree-*.sh`) |
| Codespace | Manual (`git worktree` commands) |
| CC Web | Not supported |

## Local Devcontainer

Scripts for managing worktrees in the local devcontainer:

- Create: `.devcontainer/local/worktree-new.sh [--force] [--no-hydrate] <path> <branch>`
  - Creates worktree and branch (from `main` if missing).
  - Use `--no-hydrate` to skip toolchain hydration.
- Remove: `.devcontainer/local/worktree-remove.sh <path> [--force]`
  - Removes the worktree (branch is kept).
- List: `git worktree list`

Notes for local:
- Worktrees live under `/workspaces/worktrees/`.
- Shared build cache lives under `/workspaces/worktrees/shared/` (notably Rust `target/`).

## GitHub Codespaces

Use manual git worktree commands:

```bash
git worktree add <path> <branch>
git worktree list
git worktree remove <path>
```

## Claude Code Web

Git worktrees are not supported in CC web. Use single-branch workflow.
