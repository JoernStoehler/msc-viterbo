# Development Environments

Environment configuration and git worktrees for parallel agent work.

## Environment Comparison

| Feature | Local | Codespace | CC Web |
|---------|-------|-----------|--------|
| Status | **Primary** | Backup | Emergency |
| TexLive | Yes | Yes | No |
| LaTeXML | Yes | Yes | No |
| Rust/Python | Yes | Yes | Yes |
| Git worktrees | Scripts | Manual | No |
| Skills | Work | Work | Broken |
| Cache persistence | Bind mounts | No | No |

## Environment Detection

```bash
if [[ -n "${CODESPACE:-}" ]]; then
  echo "Codespace"
elif [[ -n "${CLAUDE_CODE_REMOTE:-}" ]]; then
  echo "CC Web"
else
  echo "Local"
fi
```

## Git Worktrees

Multiple agents work in parallel on different branches. Each worktree is at `/workspaces/worktrees/<task-name>`.

**CRITICAL**: VSCode IDE extension uses `/workspaces/msc-viterbo` as working directory. Always `cd` in commands:

```bash
cd /workspaces/worktrees/<task> && cd packages/rust_viterbo && cargo build
```

### PR Merge Strategy

This repo uses **rebase+merge** (not squash, not merge commits):
- PRs rebased onto main, then fast-forwarded
- Linear history, individual commits preserved
- Structure commits logically when creating PRs

### Limitations

1. Skills and CLAUDE.md read from main repo at session start, not worktree
2. Working directory is always main repo (IDE extension behavior)
3. No shared build cache (each worktree builds independently, ~60s cold start)
4. `/workspaces/` persists across Codespace rebuilds

## Adding Dependencies

**Python** (all environments):
1. Add to `packages/python_viterbo/pyproject.toml`
2. Run `uv sync --extra dev`

**Rust** (all environments):
1. Add to `packages/rust_viterbo/*/Cargo.toml`
2. Run `cargo build`

**System** (local/codespace only):
1. Add to `.devcontainer/{local,codespace}/Dockerfile`
2. Update build scripts to fail gracefully in CC web

## Codespace Notes

- Auto-stops after idle period
- OAuth may not persist across rebuilds
- Caches don't persist across rebuilds
- `/workspaces/` persists across rebuilds

## CC Web Limitations

Emergency backup only:
- apt-get, https don't work (DNS blocked by proxy)
- Skills are broken (not auto-loaded)
- Playwright is broken (browsers not installed)
