# Environment Skill

**Purpose**: Understanding and maintaining the development environments for this thesis project.

**When to use this skill**:
- You need to understand the environment architecture (for troubleshooting, modifications, or curiosity)
- You're modifying or extending the environment setup
- You encounter environment-related errors and need deeper context than error messages provide

**When NOT to use this skill**:
- Normal thesis work (build, test, commit) - error messages guide you to install scripts automatically
- You just need to install a missing dependency - follow the error message

---

## Environment Architecture

This project supports two environments:

### 1. Local Devcontainer (Jörn's machine)
- **Defined by**: `.devcontainer/Dockerfile`, `.devcontainer/devcontainer.json`, `scripts/devcontainer-post-create.sh`
- **What it does**: Pre-installs all dependencies (TexLive, Rust, Python, Node.js, etc.) in a Docker image
- **Special features**:
  - Bind mounts for cache persistence (`/srv/devhome/*` → `/home/vscode/*`)
  - Worktrees support (`/workspaces/worktrees` for git worktree isolation)
  - Shared Rust build cache via `CARGO_TARGET_DIR=/workspaces/worktrees/shared/target`

### 2. Claude Code Web Environment
- **Defined by**: Ubuntu 24.04 base with pre-installed language runtimes (see Claude Code docs)
- **What it does**: Provides a clean environment accessible from anywhere via web browser
- **What's pre-installed**: Rust, Python (with uv), Node.js, Git, build-essential
- **What's NOT pre-installed**: TexLive, latexml
- **Key difference**: No devcontainer files run, no bind mounts, no worktrees directory

**Critical limitation (known bug as of Jan 2026):**
- apt-get does NOT work in web environment (DNS blocked by proxy architecture)
- See: [GitHub issue #14538](https://github.com/anthropics/claude-code/issues/14538)
- **Consequence**: TexLive cannot be installed, LaTeX builds are local-only
- **What works**: cargo, uv/pip, npm (HTTP proxy compatible)
- **What doesn't work**: apt-get, dpkg, any system packages

---

## Dependency Installation

### Progressive Disclosure Strategy

**Level 1: Error messages tell you what to do**
- Build/lint scripts check for dependencies and print install commands
- Example: `pdflatex not found. Please run from repo root: ./packages/latex_viterbo/scripts/install-texlive.sh (~2 min)`

**Level 2: This skill (understanding)**
- Explains environment architecture
- Documents conventions for modifications

**Level 3: Detailed implementation**
- Devcontainer config files (`.devcontainer/*`)
- Install scripts with `--help` (e.g., `packages/latex_viterbo/scripts/install-texlive.sh --help`)
- Reference docs in `references/` subdirectory (if any)

### Install Scripts

Install scripts live next to the code that uses them:
- `packages/latex_viterbo/scripts/install-texlive.sh` - Installs TexLive via apt-get (~2 min, ~1.3GB)
- `packages/python_viterbo/`: Dependencies via `uv sync` (maturin, pytest, etc.)
- `packages/rust_viterbo/`: Rust toolchain should be pre-installed in both environments

All install scripts:
- Check if already installed (idempotent)
- Print clear progress messages
- Support `--help` flag
- Document install time and disk usage

---

## Conventions for Modifying Environments

When you need to add dependencies or modify environment setup:

### 1. Document with Progressive Disclosure
- **CLAUDE.md**: Add one-line guidance ("If X fails, run Y")
- **This skill**: Explain architecture changes if significant
- **Config files**: Keep comments factual, avoid speculation
- **Install scripts**: Include --help with details

### 2. Use Install Scripts
- Create `packages/X/scripts/install-Y.sh` for heavyweight dependencies
- Make scripts idempotent (check before installing)
- Print helpful messages about time/disk usage
- Point build/lint scripts to install script in error messages

### 3. Never Make False Claims
- Future agents will believe documentation literally
- Example: Don't call a 2GB install "slim"
- Example: Don't say "everywhere" when you mean "in local devcontainer"
- When uncertain, be explicit about what you don't know

### 4. Keep It Simple (KISS)
- Follow standard patterns (apt-get, cargo, npm, pip/uv)
- Don't over-engineer for hypothetical future requirements
- Don't add noise to config files that agents don't need

### 5. Maintain Both Environments
- **Local devcontainer**: Bake dependencies into Dockerfile when reasonable
- **Web environment**: Provide install scripts, assume nothing is pre-installed except base tools
- Test changes in both environments (or document what's untested)

### 6. DRY - Don't Repeat Yourself
- Information should live in ONE canonical place
- Link to that place rather than duplicating
- Exception: Error messages can duplicate install instructions for convenience

---

## Common Tasks

### Detecting Which Environment You're In
```bash
# Web environment has this variable
if [[ -n "${CLAUDE_CODE_REMOTE:-}" ]]; then
  echo "Running in Claude Code web environment"
else
  echo "Running in local environment (or other)"
fi
```

### Adding a New Heavyweight Dependency

1. **Create install script**: `packages/X/scripts/install-Y.sh`
   - Make it idempotent
   - Add --help flag
   - Document time/disk usage

2. **Update build/lint scripts**: Add check with helpful error
   ```bash
   if ! command -v Y >/dev/null 2>&1; then
     echo "[script] ERROR: Y not found" >&2
     echo "[script] Please run: packages/X/scripts/install-Y.sh (~N min)" >&2
     exit 1
   fi
   ```

3. **Update CLAUDE.md**: Add one line to Environment Dependencies section

4. **For local devcontainer**: Consider adding to Dockerfile if it's:
   - Used frequently
   - Heavyweight (benefits from caching)
   - Stable (rarely changes)

5. **Test in web environment**: Spawn a web agent and verify the install script works

### Fixing Environment-Specific Issues

Example: Rust builds depend on `CARGO_TARGET_DIR=/workspaces/worktrees/shared/target` in local, but that dir doesn't exist in web.

**Approach**:
1. Identify the constraint (worktrees mount only exists in local)
2. Make it environment-aware (unset CARGO_TARGET_DIR in web, or create dir)
3. Document the difference in this skill if non-obvious
4. Test both environments

---

## Files to Read

- `.devcontainer/Dockerfile` - What's baked into local devcontainer image
- `.devcontainer/devcontainer.json` - Local devcontainer configuration
- `scripts/devcontainer-post-create.sh` - Local environment initialization
- `packages/*/scripts/install-*.sh` - On-demand dependency installation
- `.claude/CLAUDE.md` - Top-level environment guidance for agents
