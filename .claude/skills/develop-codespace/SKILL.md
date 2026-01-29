---
name: develop-codespace
description: Working with development environments, git worktrees for parallel agents, or modifying devcontainer configuration. Use when setting up worktrees, troubleshooting environment issues, or changing toolchain.
---

# Development Environments

## Three Environments

| Feature | Local | Codespace | CC Web |
|---------|-------|-----------|--------|
| Status | **Primary** | Backup | Emergency backup |
| TexLive | Yes | Yes | No |
| LaTeXML | Yes | Yes | No |
| Rust/Python | Yes | Yes | Yes |
| Git worktrees | Scripts | Manual | No |
| Skills | Work | Work | Broken |
| Cache persistence | Bind mounts | No | No |

**Currently using**: Local devcontainer

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

## Codespace-Specific Notes

- Auto-stops after idle period
- OAuth may not persist across rebuilds
- Caches don't persist across rebuilds
- `/workspaces/` persists across rebuilds (use for worktrees)

## Git Worktrees for Parallel Agents

### Purpose

Multiple agents work in parallel on different branches. Each worktree is an isolated working directory at `/workspaces/worktrees/<task-name>`.

### Working Pattern

**CRITICAL**: The VSCode IDE extension uses `/workspaces/msc-viterbo` as working directory. You **must** use `cd` in every bash command:

```bash
# Always cd before running commands
cd /workspaces/worktrees/<task> && cd packages/rust_viterbo && cargo build
```

### PR Merge Strategy

**This repo uses rebase+merge** (not squash, not merge commits):
- PRs are rebased onto main, then fast-forwarded
- Linear history, clean git log
- Individual commits preserved (no squashing)
- When creating PRs, structure commits logically

### Key Limitations

1. **Skills and CLAUDE.md read from main repo** at session start, not worktree
2. **Working directory is always main repo** (IDE extension behavior)
3. **No shared build cache** (each worktree builds independently, ~60s cold start for Rust)
4. **/workspaces/ persists** across Codespace rebuilds

## Modifying Environments

### Policy

- Environment changes require approval
- Make changes in devcontainer definition files (no ad-hoc local installs)
- Rebuild required after changes
- No default devcontainer.json (explicit selection required)

### Adding Dependencies

**Python packages** (works in all environments):
1. Add to `packages/python_viterbo/pyproject.toml`
2. Run `uv sync --extra dev`

**Rust crates** (works in all environments):
1. Add to `packages/rust_viterbo/*/Cargo.toml`
2. Run `cargo build`

**System dependencies** (local/codespace only):
1. Add to `.devcontainer/{local,codespace}/Dockerfile`
2. Update build scripts to fail gracefully in CC web

## CC Web Limitations (Emergency Backup Only)

- apt-get, https does NOT work (DNS blocked by proxy)
- Skills are broken (not auto-loaded)
- Playwright is broken (browsers not installed)
