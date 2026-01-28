---
name: devcontainer-maintenance
description: Maintain or change the devcontainer environments for this repo. Use when editing .devcontainer files, changing toolchains, or requesting environment rebuilds.
---

# Devcontainer Maintenance

## Source of Truth

Three environments, each with its own config:

| Environment | Config Location |
|-------------|-----------------|
| Local | `.devcontainer/local/` |
| Codespace | `.devcontainer/codespace/` |
| CC Web | `.devcontainer/ccweb/` (docs only) |

Shared files:
- `.devcontainer/scripts/post-create.sh` - Post-create script (env-aware)
- `.devcontainer/scripts/warmup-cache.sh` - Background cache warming
- `.devcontainer/README.md` - Overview documentation
- `setup.sh` - Catnip workspace setup (repo root)

## Policy

- Environment changes must be approved by the project owner.
- Make changes in the devcontainer definition files (no ad-hoc local installs).
- Rebuild required after changes.
- No default devcontainer.json - explicit selection required.

## Local Environment

Full-featured development with TexLive and bind mounts.

```bash
# From host machine:
.devcontainer/local/host-devcontainer-rebuild.sh
.devcontainer/local/host-vscode-tunnel.sh
```

Files:
- `.devcontainer/local/devcontainer.json`
- `.devcontainer/local/Dockerfile`
- `.devcontainer/local/host-devcontainer-rebuild.sh`
- `.devcontainer/local/host-vscode-tunnel.sh`

Notes:
- Bind mounts to `/srv/devhome/*` for cache persistence
- Worktrees at `/workspaces/worktrees/`
- Shared Rust cache: `CARGO_TARGET_DIR=/workspaces/worktrees/shared/target`

## Codespace Environment

Cloud development with catnip for worktree management.

```bash
gh codespace create -r JoernStoehler/msc-viterbo \
    --devcontainer-path .devcontainer/codespace/devcontainer.json
```

Files:
- `.devcontainer/codespace/devcontainer.json`
- `.devcontainer/codespace/Dockerfile`

Notes:
- No TexLive (saves 2GB)
- Catnip feature for git worktrees
- Port 6369 forwarded for catnip
- `setup.sh` in repo root for catnip workspace init (currently disabled)

## CC Web Environment

No devcontainer - documentation only.

Files:
- `.devcontainer/ccweb/README.md`

Notes:
- apt-get blocked (DNS proxy bug)
- Skills broken
- Playwright browsers unavailable
