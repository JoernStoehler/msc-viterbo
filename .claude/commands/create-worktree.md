Before you start, please setup a Git worktree for you to work in:

```bash
cd /workspaces/msc-viterbo
git worktree add /workspaces/worktrees/<task> -b <branch-name>
# Example:
cd /workspaces/msc-viterbo
git worktree add /workspaces/worktrees/fix-billiard-bug -b fix/billiard-bug
```

Tell the user about the chosen worktree and branch. Remember both.

**IMPORTANT**: Always use `cd /workspaces/worktrees/<task>` before running any commands to ensure you are working in the correct context, otherwise you will default to the protected main worktree.

After you are told that the PR is merged, please clean up your worktree with:

```bash
git worktree remove /workspaces/worktrees/<task>
```

The rest of the user's message at this time is:

$ARGUMENTS
