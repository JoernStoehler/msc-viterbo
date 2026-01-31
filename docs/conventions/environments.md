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
| Plugins | CLI only | CLI only | Unknown |
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

## VSCode IDE Extension vs CLI

The VSCode IDE extension and Claude Code CLI are different products with different capabilities.

**Key difference: Plugins**
- Official Claude Code docs (https://code.claude.com/docs) describe CLI features
- IDE extension has partial/buggy plugin support:
  - `/plugin install` and `/plugin marketplace add` produce no output (unclear if success/failure)
  - `/plugin` GUI opens but may show empty state
  - GUI breaks when using search
- **Use CLI for plugin management** - it works reliably

**Plugin installation (one-time setup via CLI):**
```bash
claude plugin marketplace add anthropics/claude-plugins-official
claude plugin install rust-analyzer-lsp@claude-plugins-official --scope project
claude plugin install pyright-lsp@claude-plugins-official --scope project
```

Plugins installed at project scope are stored in `.claude/settings.json` and available to future sessions.

**References:**
- Official plugins: https://github.com/anthropics/claude-plugins-official
- Demo plugins: https://github.com/anthropics/claude-code/tree/main/plugins

## CC Web Limitations

Emergency backup only:
- apt-get, https don't work (DNS blocked by proxy)
- Skills are broken (not auto-loaded)
- Playwright is broken (browsers not installed)
