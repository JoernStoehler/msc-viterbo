---
name: develop-codespace
description: Maintain or change the devcontainer environments for this repo. Use when editing .devcontainer files, changing toolchains, or requesting environment rebuilds.
---

# Codespace Development Environment

**When to use this skill:**
- You're modifying or extending the environment setup
- You encounter environment-related errors and need deeper context
- You need to understand git worktrees for parallel agent workflows
- You're troubleshooting environment issues

---

## Environment Architecture

This project supports **three environments**:

| Environment | Config Location | Use Case |
|-------------|-----------------|----------|
| **Codespace** | `.devcontainer/codespace/` | **Primary** - GitHub Codespaces |
| Local | `.devcontainer/local/` | Jörn's Ubuntu desktop |
| CC Web | `.devcontainer/ccweb/` (docs only) | Claude Code Web |

### Codespace (Primary Environment)

- **Defined by**: `.devcontainer/codespace/devcontainer.json`, `.devcontainer/codespace/Dockerfile`
- **Post-create**: `.devcontainer/scripts/post-create.sh`
- **What it does**: Cloud dev environment
- **Special features**:
  - Full TexLive installation for PDF builds
  - LaTeXML for HTML conversion
  - Manual git worktrees via `git worktree` commands
  - Parallel agent workflows (worktrees + IDE extension)
- **Known limitations**:
  - Auto-stops after idle period
  - OAuth may not persist across rebuilds
  - Caches don't persist across rebuilds

### Local Devcontainer

- **Defined by**: `.devcontainer/local/devcontainer.json`, `.devcontainer/local/Dockerfile`
- **Post-create**: `.devcontainer/scripts/post-create.sh`
- **Host scripts**: `.devcontainer/local/host-*.sh`
- **Special features**:
  - Bind mounts for cache persistence (`/srv/devhome/*` → `/home/vscode/*`)
  - Manual git worktrees via `/workspaces/worktrees/`
  - Shared Rust build cache via `CARGO_TARGET_DIR=/workspaces/worktrees/shared/target`
  - Full TexLive installation for PDF builds
  - VS Code tunnel for remote access

### Claude Code Web

- **Defined by**: Ubuntu 24.04 base (no devcontainer)
- **Docs**: `.devcontainer/ccweb/README.md`
- **What's pre-installed**: Rust, Python (with uv), Node.js, Git, build-essential
- **What's NOT pre-installed**: TexLive, latexml, Playwright browsers

**Critical limitations (as of Jan 2026):**
- apt-get does NOT work (DNS blocked by proxy architecture)
- Skills are broken (names/descriptions not autoloaded)
- Playwright cannot install browsers
- No git worktrees support

---

## What's Available Where

| Feature | Local | Codespace | CC Web |
|---------|-------|-----------|--------|
| TexLive (pdflatex, chktex) | Yes | Yes | No |
| latexml | Yes | Yes | No |
| Rust (cargo, rustc) | Yes | Yes | Yes |
| Python + uv | Yes | Yes | Yes |
| gh CLI | Yes | Yes | Auto-installed |
| Playwright | Yes | Yes | No |
| Git worktrees | Manual scripts | Manual | No |
| Parallel agents | Scripts | Worktrees + IDE | No |
| Cache persistence | Bind mounts | No | No |
| Skills | Work | Work | Broken |

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

## Modifying Environments

### Policy

- Environment changes must be approved by the project owner.
- Make changes in the devcontainer definition files (no ad-hoc local installs).
- Rebuild required after changes.
- No default devcontainer.json - explicit selection required.

### Shared Files

- `.devcontainer/scripts/post-create.sh` - Post-create script (env-aware)
- `.devcontainer/scripts/warmup-cache.sh` - Background cache warming
- `.devcontainer/README.md` - Overview documentation

### Adding Dependencies

**For Python packages** (works in all environments):
1. Add to `packages/python_viterbo/pyproject.toml`
2. Run `uv sync --extra dev`

**For Rust crates** (works in all environments):
1. Add to `packages/rust_viterbo/*/Cargo.toml`
2. Run `cargo build`

**For system dependencies** (local/codespace only):
1. Add to `.devcontainer/local/Dockerfile` and/or `.devcontainer/codespace/Dockerfile`
2. Update build scripts to fail gracefully in CC web

### Creating a Codespace

```bash
gh codespace create -r JoernStoehler/msc-viterbo \
    --devcontainer-path .devcontainer/codespace/devcontainer.json
```

### Running Local Devcontainer

```bash
# From host machine:
.devcontainer/local/host-devcontainer-rebuild.sh
.devcontainer/local/host-vscode-tunnel.sh
```

---

## Git Worktrees for Parallel Agents

### Purpose

Git worktrees enable multiple agents to work in parallel on different branches without interfering with each other. Each worktree is an isolated working directory with its own branch and files, while sharing the same Git history.

### Quick Start (Codespaces + IDE Extension)

#### Setup

```bash
# Create worktree for your task
git worktree add /workspaces/worktrees/<task-name> -b <branch-name>

# Example:
git worktree add /workspaces/worktrees/fix-billiard-bug -b fix-billiard-bug
```

#### Working Pattern

**CRITICAL**: The VSCode IDE extension uses `/workspaces/msc-viterbo` as the working directory. You **must** use `cd` in every bash command:

```bash
# Always cd before running commands
cd /workspaces/worktrees/fix-billiard-bug && cargo test
cd /workspaces/worktrees/fix-billiard-bug && git status
cd /workspaces/worktrees/fix-billiard-bug && scripts/test-rust.sh

# Chain multiple commands
cd /workspaces/worktrees/fix-billiard-bug && cargo fmt && cargo clippy && git add .
```

#### Common Operations

```bash
# Run Rust tests
cd /workspaces/worktrees/<task-name> && cargo test

# Run Python tests
cd /workspaces/worktrees/<task-name> && cd packages/python_viterbo && uv run pytest

# Format and lint Rust
cd /workspaces/worktrees/<task-name> && cargo fmt --all
cd /workspaces/worktrees/<task-name> && cargo clippy --workspace

# Git operations
cd /workspaces/worktrees/<task-name> && git status
cd /workspaces/worktrees/<task-name> && git add .
cd /workspaces/worktrees/<task-name> && git commit -m "Fix bug"
cd /workspaces/worktrees/<task-name> && git push -u origin <branch-name>
```

#### Cleanup

After your PR is merged:

```bash
# Remove the worktree (branch stays on GitHub as PR history)
git worktree remove /workspaces/worktrees/<task-name>

# Verify it's gone
git worktree list
```

### Key Limitations

#### 1. Skills and CLAUDE.md Read from Main Repo

The VSCode IDE extension operates from `/workspaces/msc-viterbo`, so:
- Skills in `.claude/skills/` are read from **main repo**, not your worktree
- `CLAUDE.md` is read from **main repo**, not your worktree
- Custom commands in `.claude/commands/` are from **main repo**

**Implication**: This workflow works best when worktrees don't diverge significantly from `main` in terms of workflow docs.

#### 2. Working Directory Behavior

The IDE extension sets its working directory to the **root folder** of the VSCode window (`/workspaces/msc-viterbo`). You cannot change this via `cd` commands in bash — you must explicitly `cd` in every bash command you run.

#### 3. No Shared Build Cache

Each worktree builds independently. Cold start takes ~60 seconds to build Rust crates. This is acceptable for parallel agent workflows.

#### 4. VSCode Multi-Root Workspace Bug

There's a [known bug](https://github.com/anthropics/claude-code/issues/8559) where the IDE extension always uses the first folder in multi-root workspaces. **Workaround**: Don't use multi-root workspaces — use separate browser tabs or the terminal CLI if you need true parallelism.

### Persistence Across Rebuilds

Worktrees under `/workspaces/` persist across Codespace container rebuilds. This is the **only** directory that survives rebuilds, so always use `/workspaces/worktrees/` for worktrees.

### Alternative: Terminal CLI for Parallelism

If the IDE extension's `cd` requirement becomes too high friction, fall back to the terminal CLI:

```bash
# Create worktree
git worktree add /workspaces/worktrees/task-a -b task-a

# Open new terminal tab/pane in VSCode
cd /workspaces/worktrees/task-a
claude  # Run CLI session here
```

Terminal CLI sessions:
- Have full feature parity with IDE extension
- Operate in the directory where you run `claude`
- Support tmux/screen for session management
- Lack the GUI's visual polish (diffs, nice rendering)

### Worktree Commands Reference

```bash
# List all worktrees
git worktree list

# Remove a worktree
git worktree remove <path>

# Remove a worktree with uncommitted changes (force)
git worktree remove <path> --force

# Prune stale worktree references
git worktree prune
```

### Workflow Example

```bash
# 1. Agent receives task: "Fix billiard trajectory bug"
git worktree add /workspaces/worktrees/fix-billiard -b fix-billiard

# 2. Work in the worktree (remember to cd!)
cd /workspaces/worktrees/fix-billiard && cargo test --package billiard
# ... fix the bug ...
cd /workspaces/worktrees/fix-billiard && cargo test --package billiard
cd /workspaces/worktrees/fix-billiard && git add .
cd /workspaces/worktrees/fix-billiard && git commit -m "Fix billiard trajectory calculation"
cd /workspaces/worktrees/fix-billiard && git push -u origin fix-billiard

# 3. Create PR (can run from anywhere since gh uses remote)
gh pr create --title "Fix billiard trajectory calculation" --body "..."

# 4. After PR merge, clean up
git worktree remove /workspaces/worktrees/fix-billiard
```

---

## Files to Read

- `.devcontainer/README.md` - Overview of all environments
- `.devcontainer/local/devcontainer.json` - Local config
- `.devcontainer/codespace/devcontainer.json` - Codespace config
- `.devcontainer/ccweb/README.md` - CC web limitations
- `.devcontainer/scripts/post-create.sh` - Shared post-create script
