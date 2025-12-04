# Add a Git Worktree
- We isolate the workdirs of agents using Git worktrees.
- Creation: `scripts/worktree-new.sh <path> <branch> [--force]`: validates, adds worktree and branch from `main`, hydrates toolchains.
- Removal: `scripts/worktree-remove.sh <path> [--force]`: validates, removes worktree and branch.
- List: `git worktree list`