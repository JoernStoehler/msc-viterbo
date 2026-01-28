---
name: develop-codespace
description: Working with development environments, git worktrees for parallel agents, or modifying devcontainer configuration. Use when setting up worktrees, troubleshooting environment issues, or changing toolchain.
---

# Development Environments

## Three Environments

| Feature | Local | Codespace | CC Web |
|---------|-------|-----------|--------|
| Status | Backup | **Primary** | Emergency backup |
| TexLive | Yes | Yes | No |
| LaTeXML | Yes | Yes | No |
| Rust/Python | Yes | Yes | Yes |
| Git worktrees | Scripts | Manual | No |
| Skills | Work | Work | Broken |
| Cache persistence | Bind mounts | No | No |

**Currently using**: GitHub Codespaces

## Environment Detection

```bash
if [[ "${DEVCONTAINER_ENV:-}" == "codespace" ]]; then
  echo "Codespace"
elif [[ -n "${CODESPACES:-}" ]]; then
  echo "Codespace (env var not set)"
elif [[ -n "${CLAUDE_CODE_REMOTE:-}" ]]; then
  echo "CC Web"
fi
```

## Codespace-Specific Notes

- Auto-stops after idle period
- OAuth may not persist across rebuilds
- Caches don't persist across rebuilds
- `/workspaces/` persists across rebuilds (use for worktrees)

## Creating Codespace

```bash
gh codespace create -r JoernStoehler/msc-viterbo \
    --devcontainer-path .devcontainer/codespace/devcontainer.json
```

## Git Worktrees for Parallel Agents

### Purpose

Enable multiple agents to work in parallel on different branches without interfering. Each worktree is an isolated working directory with its own branch and files, sharing the same Git history.

### Setup

```bash
# Create worktree for your task
git worktree add /workspaces/worktrees/<task-name> -b <branch-name>

# Example:
git worktree add /workspaces/worktrees/fix-billiard-bug -b fix-billiard-bug
```

### Working Pattern

**CRITICAL**: The VSCode IDE extension uses `/workspaces/msc-viterbo` as working directory. You **must** use `cd` in every bash command:

```bash
# Always cd before running commands
cd /workspaces/worktrees/<task> && cargo test
cd /workspaces/worktrees/<task> && git status
cd /workspaces/worktrees/<task> && uv run pytest

# Chain multiple commands
cd /workspaces/worktrees/<task> && cargo fmt && cargo clippy && git add .
```

### Common Operations

```bash
# Rust tests
cd /workspaces/worktrees/<task> && cargo test

# Python tests
cd /workspaces/worktrees/<task> && cd packages/python_viterbo && uv run pytest

# Format and lint
cd /workspaces/worktrees/<task> && cargo fmt --all
cd /workspaces/worktrees/<task> && cargo clippy --workspace

# Git operations
cd /workspaces/worktrees/<task> && git status
cd /workspaces/worktrees/<task> && git add .
cd /workspaces/worktrees/<task> && git commit -m "Fix bug"
cd /workspaces/worktrees/<task> && git push -u origin <branch>
```

### Cleanup

After your PR is merged:

```bash
# Remove the worktree (branch stays on GitHub as PR history)
git worktree remove /workspaces/worktrees/<task>

# Verify it's gone
git worktree list
```

### Key Limitations

1. **Skills and CLAUDE.md read from main repo**, not worktree
2. **Working directory is always main repo** (IDE extension behavior)
3. **No shared build cache** (each worktree builds independently, ~60s cold start for Rust)
4. **/workspaces/ persists** across Codespace rebuilds

### Alternative: Terminal CLI

If the IDE extension's `cd` requirement becomes too high friction:

```bash
# Create worktree
git worktree add /workspaces/worktrees/<task> -b <branch>

# Open new terminal tab/pane in VSCode
cd /workspaces/worktrees/<task>
claude  # Run CLI session here
```

Terminal CLI sessions:
- Have full feature parity with IDE extension
- Operate in the directory where you run `claude`
- Support tmux/screen for session management
- Lack the GUI's visual polish

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

- apt-get does NOT work (DNS blocked by proxy)
- Skills are broken (not auto-loaded)
- No Playwright browsers
- No git worktrees support
