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
cd /workspaces/worktrees/<task> && cd crates && cargo build
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
1. Add to `crates/*/Cargo.toml`
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

**LSP plugins: broken, do not use (tested 2026-01-31)**

Most LSP operations return empty/useless results. Use Grep and Glob for code navigation instead. See `docs/notes/lsp-investigation.md` for details.

## Claude Code Configuration

**Config file locations:**
- `$CLAUDE_CONFIG_DIR/.claude.json` - User-level settings (install method, theme, account info)
- `.claude/settings.json` - Project-level settings (permissions, hooks, plugins)
- `.claude/settings.local.json` - Personal project settings (gitignored)

**CLAUDE_CONFIG_DIR environment variable:**
- Default: `$HOME` (so `.claude.json` lands at `~/.claude.json`)
- This project sets it to `/home/vscode/.claude` in devcontainer.json
- Why: The bind mount only covers `~/.claude/` directory. Without this envvar, `.claude.json` would be at home root (outside the mount) and lost on rebuild.

**Permission modes:**
```json
{
  "permissions": {
    "defaultMode": "bypassPermissions"
  }
}
```

Valid modes: `"default"`, `"acceptEdits"`, `"bypassPermissions"`, `"plan"`

This project uses `bypassPermissions` since we run in a sandboxed container.

**Known /doctor false positive:**
The `/doctor` command may show "Warning: Leftover npm global installation" even when no npm install exists. This happens when npm's prefix is `~/.local` (same as native install location). The detection logic incorrectly assumes `~/.local/bin/claude` came from npm. Safe to ignore if `~/.claude.json` shows `"installMethod": "native"`.

## CC Web Limitations

Emergency backup only:
- apt-get, https don't work (DNS blocked by proxy)
- Skills are broken (not auto-loaded)
- Playwright is broken (browsers not installed)
