# Development Environments

This project supports three development environments:

| Environment | Folder | Use Case |
|-------------|--------|----------|
| **Local** | `local/` | Jörn's Ubuntu desktop with bind mounts |
| **Codespace** | `codespace/` | GitHub Codespaces |
| **CC Web** | `ccweb/` | Claude Code Web (no devcontainer) |

## Quick Comparison

| Feature | Local | Codespace | CC Web |
|---------|-------|-----------|--------|
| TexLive (PDF builds) | Yes | Yes | No |
| LaTeXML (HTML) | Yes | Yes | No |
| Cache persistence | Bind mounts | No | No |
| Git worktrees | Manual scripts | Manual | No |
| Parallel agents | Scripts | Worktrees + IDE | No |
| Skills | Work | Work | Broken |
| Status | **Primary** | Backup | Emergency backup |

## Local (`local/`)

Full-featured environment for Jörn's Ubuntu desktop.

```bash
# From host machine:
.devcontainer/local/host-devcontainer-rebuild.sh
.devcontainer/local/host-vscode-tunnel.sh
```

Prerequisites:
- `/srv/devhome/` directories for cache persistence
- `/srv/devworktrees/msc-viterbo/worktrees/` for git worktrees
- `npm i -g @devcontainers/cli`

## Codespace (`codespace/`)

GitHub Codespaces for remote development. Backup environment when Local is unavailable.

```bash
# Create codespace:
gh codespace create -r JoernStoehler/msc-viterbo \
    --devcontainer-path .devcontainer/codespace/devcontainer.json
```

Pre-installed:
- Rust (stable with rustfmt, clippy)
- Python 3 with uv
- Node.js 22
- GitHub CLI
- TexLive (latex-base, latex-extra, science packages)
- LaTeXML for HTML conversion

Known limitations:
- Auto-stops after idle period
- OAuth may not persist across rebuilds
- Caches don't persist

## CC Web (`ccweb/`)

Claude Code Web at claude.ai/code. No devcontainer needed.

See `ccweb/README.md` for details and limitations.

## Adding Dependencies

**Python** (all environments):
1. Add to `experiments/pyproject.toml`
2. Run `uv sync --extra dev`

**Rust** (all environments):
1. Add to `crates/*/Cargo.toml`
2. Run `cargo build`

**System** (local/codespace only):
1. Add to `.devcontainer/{local,codespace}/Dockerfile`
2. Update build scripts to fail gracefully in CC Web

## No Default Configuration

There is intentionally no root `devcontainer.json`. Users must explicitly
select `local/` or `codespace/` to avoid accidentally using the wrong
environment.
