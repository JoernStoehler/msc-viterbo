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
| TexLive (PDF builds) | Yes | No | No |
| Cache persistence | Bind mounts | No | No |
| Git worktrees | Manual scripts | Manual | No |
| Skills | Work | Should work | Broken |
| Startup time | Fast | Fast | Fast |
| Friction | Medium | Low | Low |

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

GitHub Codespaces for remote development. Uses devcontainer features for fast startup.

```bash
# Create codespace:
gh codespace create -r JoernStoehler/msc-viterbo \
    --devcontainer-path .devcontainer/codespace/devcontainer.json
```

Pre-installed via features:
- Rust (stable with rustfmt, clippy)
- Python 3.12 with uv
- Node.js 22
- GitHub CLI

Known limitations:
- **No TexLive** - use local devcontainer for PDF builds
- Auto-stops after idle period
- OAuth may not persist across rebuilds
- Caches don't persist

## CC Web (`ccweb/`)

Claude Code Web at claude.ai/code. No devcontainer needed.

See `ccweb/README.md` for details and limitations.

## No Default Configuration

There is intentionally no root `devcontainer.json`. Users must explicitly
select `local/` or `codespace/` to avoid accidentally using the wrong
environment.
