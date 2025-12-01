# Maintain Environment Caches
- Purpose: Speed up builds by sharing caches across git worktrees and devcontainer rebuilds.
- Rust: `.cargo/config.toml` sets `target-dir = "/workspaces/worktrees/shared/target"` so all worktrees reuse builds. Clean only when corrupted (`rm -rf /workspaces/worktrees/shared/target/<crate>`).
- Lean: `scripts/worktree-prepare.sh` links `.lake/packages` to `/workspaces/worktrees/shared/lean/packages` and runs `lake exe cache get`. Build output is shared via `.lake/build -> /workspaces/worktrees/shared/lean/build-global`. If mathlib looks broken, drop `/workspaces/worktrees/shared/lean/packages/*` and rerun the prep script.
- Python: uv uses the host-mounted `$HOME/.cache/uv`. Each worktree keeps its own `.venv` under `packages/python_viterbo/`; delete and rerun `uv sync --locked --extra dev` if the venv gets wedged.
- Node: `scripts/devcontainer-post-create.sh` sets npm prefix/cache to `$HOME/.local` and `$HOME/.cache/npm`, both bind-mounted, so global installs survive container rebuilds.
- Worktree mount: `/workspaces/worktrees` is a host bind; anything you stash there (shared targets, Lean caches, git worktrees) persists across devcontainer rebuilds.
