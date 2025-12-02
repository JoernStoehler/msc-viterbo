# Maintain Environment (extended reference)

Purpose
- Single reproducible devcontainer; no ad‑hoc local installs. Everything lives in `.devcontainer/*`, `scripts/devcontainer-post-create.sh`, `scripts/worktree-prepare.sh`, `msc-viterbo.code-workspace`.

Base image
- `mcr.microsoft.com/devcontainers/base:ubuntu` with Rust, Python+uv, Lean, Node, TeX Live + latexml, and common CLIs baked in.
- Small extras baked in: `inotifywait` (`inotify-tools`), `entr`, `code-tunnel`.

Host binds (see `devcontainer.json`)
- uv cache, sccache, TeX Live user caches, npm cache/prefix, gh config, worktrees under `/workspaces/worktrees`. These host dirs should already exist; if a mount is missing, create it on the host and rebuild.

Post-create
- Installs Codex CLI, warms TeX formats. VS Code tunnel is already in the image. No ar5ivist/HTML Docker flow is used.

Worktrees
- After `git worktree add <path> <branch>`, run `scripts/worktree-prepare.sh <path>` once. It syncs uv deps for python_viterbo, links Lean caches, and fetches Rust deps into the shared target.

Shared caches (per tools)
- Rust: target at `/workspaces/worktrees/shared/target`; sccache at `/home/vscode/.cache/sccache` (bind-mounted).
- Lean: `/workspaces/worktrees/shared/lean/{packages,build-global}` via symlinks created by the prep script.
- Python: uv cache bind-mounted at `/home/vscode/.cache/uv`; per-worktree `.venv` under `packages/python_viterbo/`.
- Node: npm cache/prefix `/home/vscode/.cache/npm`, `/home/vscode/.local` (set in post-create).
- TeX Live: user caches `/home/vscode/.texlive2023`, `.texmf-var`, `.texmf-config`; remove only if corrupted.

LaTeX builds
- Local `latexmk`/`latexmlc`; no Docker socket required.
