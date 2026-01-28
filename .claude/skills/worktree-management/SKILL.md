---
name: worktree-management
description: Manage git worktrees for this repo. Environment-dependent - local uses manual scripts, Codespaces use catnip.
---

# Worktree Management

## Environment-Dependent

Worktree management differs by environment:

| Environment | Worktree Method |
|-------------|-----------------|
| Local | Manual scripts (`scripts/worktree-*.sh`) |
| Codespace | Catnip (automatic via `refs/catnip/*`) |
| CC Web | Not supported |

## Local Devcontainer (DEPRECATED scripts)

The following scripts are **deprecated** and will be removed once catnip workflow is validated:

- Create: `scripts/worktree-new.sh [--force] [--no-hydrate] <path> <branch>`
  - Creates worktree and branch (from `main` if missing).
  - Use `--no-hydrate` to skip toolchain hydration.
- Remove: `scripts/worktree-remove.sh <path> [--force]`
  - Removes the worktree (branch is kept).
- List: `git worktree list`

Notes for local:
- Worktrees live under `/workspaces/worktrees/`.
- Shared build cache lives under `/workspaces/worktrees/shared/` (notably Rust `target/`).

## GitHub Codespaces (Catnip)

In Codespaces, catnip automatically manages worktrees:

- Creates worktrees via `refs/catnip/<name>` branches
- Syncs to feature branches like `feature/make-something-great`
- Access changes locally: `git checkout feature/<name>`

See: https://github.com/wandb/catnip

## Claude Code Web

Git worktrees are not supported in CC web. Use single-branch workflow.
