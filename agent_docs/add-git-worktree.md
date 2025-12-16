# Add a Git Worktree
- We isolate the workdirs of agents using Git worktrees.
- Creation: `scripts/worktree-new.sh [--force] [--no-hydrate] <path> <branch>`: validates, adds worktree and branch (creates it from `main` if missing). Default hydrates toolchains; use `--no-hydrate` to skip.
- Removal: `scripts/worktree-remove.sh <path> [--force]`: validates and removes the worktree (branch is kept).
- List: `git worktree list`
