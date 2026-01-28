Set up a git worktree for parallel agent work on task: **$ARGUMENTS**

1. Create the worktree: `git worktree add /workspaces/worktrees/$ARGUMENTS -b $ARGUMENTS`
2. **CRITICAL**: Use `cd /workspaces/worktrees/$ARGUMENTS && command` for ALL operations (IDE extension stays in main repo)
3. Read `develop-codespace` skill for full details and common operations
