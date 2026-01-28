---
name: environment
description: Understanding and maintaining the development environments for this thesis project. Use for environment architecture, troubleshooting, or modifying environment setup.
---

# Environment Skill

**When to use this skill**:
- You need to understand the environment architecture (for troubleshooting, modifications, or curiosity)
- You're modifying or extending the environment setup
- You encounter environment-related errors and need deeper context than error messages provide

**When NOT to use this skill**:
- Normal thesis work (build, test, commit) - error messages explain limitations
- You encounter a "local devcontainer only" error - the error message is sufficient

---

## Environment Architecture

This project supports **three environments**:

| Environment | Config Location | Use Case |
|-------------|-----------------|----------|
| Local | `.devcontainer/local/` | Jörn's Ubuntu desktop |
| Codespace | `.devcontainer/codespace/` | GitHub Codespaces + catnip |
| CC Web | `.devcontainer/ccweb/` (docs only) | Claude Code Web |

### 1. Local Devcontainer (Jörn's machine)

- **Defined by**: `.devcontainer/local/devcontainer.json`, `.devcontainer/local/Dockerfile`
- **Post-create**: `.devcontainer/scripts/post-create.sh`
- **Host scripts**: `.devcontainer/local/host-*.sh`
- **What it does**: Full-featured dev environment with all dependencies
- **Special features**:
  - Bind mounts for cache persistence (`/srv/devhome/*` → `/home/vscode/*`)
  - Manual git worktrees via `/workspaces/worktrees/`
  - Shared Rust build cache via `CARGO_TARGET_DIR=/workspaces/worktrees/shared/target`
  - Full TexLive installation for PDF builds
  - VS Code tunnel for remote access

### 2. GitHub Codespaces

- **Defined by**: `.devcontainer/codespace/devcontainer.json`, `.devcontainer/codespace/Dockerfile`
- **Post-create**: `.devcontainer/scripts/post-create.sh`
- **Catnip setup**: `setup.sh` (in repo root, currently disabled)
- **What it does**: Cloud dev environment with catnip for worktree management
- **Special features**:
  - Catnip feature for git worktree management and mobile access
  - No TexLive (saves 2GB, PDF builds require local)
  - Port 6369 forwarded for catnip
- **Known limitations**:
  - Auto-stops after idle period
  - OAuth may not persist across rebuilds
  - Caches don't persist across rebuilds

### 3. Claude Code Web Environment

- **Defined by**: Ubuntu 24.04 base (no devcontainer)
- **Docs**: `.devcontainer/ccweb/README.md`
- **What it does**: Lightweight environment accessible via claude.ai/code
- **What's pre-installed**: Rust, Python (with uv), Node.js, Git, build-essential
- **What's NOT pre-installed**: TexLive, latexml, Playwright browsers

**Critical limitations (as of Jan 2026):**
- apt-get does NOT work (DNS blocked by proxy architecture)
- Skills are broken (names/descriptions not autoloaded)
- Playwright cannot install browsers
- No git worktrees support

---

## Environment Detection

```bash
# Devcontainer environment (local or codespace)
if [[ "${DEVCONTAINER_ENV:-}" == "local" ]]; then
  echo "Running in local devcontainer"
elif [[ "${DEVCONTAINER_ENV:-}" == "codespace" ]]; then
  echo "Running in GitHub Codespace"
elif [[ -n "${CODESPACES:-}" ]]; then
  echo "Running in Codespace (env var not set)"
elif [[ -n "${CLAUDE_CODE_REMOTE:-}" ]]; then
  echo "Running in Claude Code Web"
else
  echo "Unknown environment"
fi
```

---

## What's Available Where

| Feature | Local | Codespace | CC Web |
|---------|-------|-----------|--------|
| TexLive (pdflatex, chktex) | Yes | No | No |
| latexml | Yes | No | No |
| Rust (cargo, rustc) | Yes | Yes | Yes |
| Python + uv | Yes | Yes | Yes |
| gh CLI | Yes | Yes | Auto-installed |
| Playwright | Yes | Yes | No |
| Git worktrees | Manual scripts | Catnip auto | No |
| Cache persistence | Bind mounts | No | No |
| Skills | Work | Should work | Broken |

---

## Conventions for Modifying Environments

### 1. Colocate Configuration
- Environment-specific files go in `.devcontainer/<env>/`
- Shared scripts go in `.devcontainer/scripts/`
- Documentation lives alongside config files

### 2. Environment-Aware Scripts
- Use `DEVCONTAINER_ENV` to detect environment
- Fail gracefully with clear error messages
- Support `--help` flag

### 3. Never Make False Claims
- Future agents will believe documentation literally
- Be explicit about what's untested
- Document known limitations

### 4. Keep It Simple (KISS)
- Follow standard patterns
- Don't over-engineer for hypothetical requirements
- No default devcontainer.json (explicit selection required)

---

## Common Tasks

### Adding a New Dependency

**For Python packages** (works in all environments):
1. Add to `packages/python_viterbo/pyproject.toml`
2. Run `uv sync --extra dev`

**For Rust crates** (works in all environments):
1. Add to `packages/rust_viterbo/*/Cargo.toml`
2. Run `cargo build`

**For system dependencies** (local only):
1. Add to `.devcontainer/local/Dockerfile`
2. Optionally add to `.devcontainer/codespace/Dockerfile`
3. Update build scripts to fail gracefully in CC web

### Running Local Devcontainer

```bash
# From host machine:
.devcontainer/local/host-devcontainer-rebuild.sh
.devcontainer/local/host-vscode-tunnel.sh
```

### Creating a Codespace

```bash
gh codespace create -r JoernStoehler/msc-viterbo \
    --devcontainer-path .devcontainer/codespace/devcontainer.json
```

---

## Files to Read

- `.devcontainer/README.md` - Overview of all environments
- `.devcontainer/local/devcontainer.json` - Local config
- `.devcontainer/codespace/devcontainer.json` - Codespace config
- `.devcontainer/ccweb/README.md` - CC web limitations
- `.devcontainer/scripts/post-create.sh` - Shared post-create script
- `setup.sh` - Catnip workspace setup (currently disabled)
