# .devcontainer/CLAUDE.md

Environment configurations (local, codespace, ccweb).

## Structure

```
.devcontainer/
  local/          # Jörn's Ubuntu desktop (primary)
    devcontainer.json
    Dockerfile
    post-create.sh
    host-devcontainer-rebuild.sh
    host-vscode-tunnel.sh
    worktree-new.sh
    worktree-remove.sh
  codespace/     # GitHub Codespaces (backup)
    devcontainer.json
    Dockerfile
    ...
  ccweb/          # Claude Code Web (emergency)
    README.md
  scripts/        # Shared scripts
    setup-common.sh
    warmup-cache.sh
```

## Dependencies

For system dependencies: `{local,codespace}/{Dockerfile,post-create.sh}` (not available in ccweb).
See `{crates,experiments,thesis}/CLAUDE.md` for Rust, Python, LaTeX dependency management.

## See Also

- Skill `cc-web-workarounds` for Claude Code Web specific instructions.
