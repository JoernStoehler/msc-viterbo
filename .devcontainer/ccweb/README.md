# Claude Code Web Environment

This folder documents the Claude Code Web (CC web) environment. There is no
`devcontainer.json` here because CC web does not use devcontainers.

## What is CC web?

Claude Code Web is Anthropic's hosted environment at claude.ai/code. It provides
a VM with pre-installed tooling where Claude agents can execute code.

**Lowest friction**: Just spawn an agent and let it work while chatting.

## Pre-installed (as of Jan 2026)

- Ubuntu 24.04 base
- Rust (cargo, rustc, rustfmt, clippy)
- Python 3 with uv
- Node.js with npm
- Git, build-essential

## NOT available

| Missing | Reason | Workaround |
|---------|--------|------------|
| TexLive | apt-get blocked (DNS proxy bug) | Use local devcontainer |
| latexml | apt-get blocked | Use local devcontainer |
| System packages | apt-get blocked | None |
| Playwright browsers | Cannot install browsers | Use local/codespace |
| git worktrees | No persistent storage | Single-branch workflow |

## Known bugs (as of Jan 2026)

1. **apt-get blocked**: DNS proxy architecture blocks apt-get/dpkg.
   See: https://github.com/anthropics/claude-code/issues/14538

2. **Skills broken**: Skill descriptions and names are not autoloaded.
   Agents often remain unaware of skills. No known workaround.
   Skills work correctly in local devcontainer and (presumably) Codespaces.

3. **Playwright cannot install browsers**: JS-heavy websites cannot be accessed.
   Limits literature search capabilities.

## Environment detection

```bash
if [[ -n "${CLAUDE_CODE_REMOTE:-}" ]]; then
    echo "Running in Claude Code Web"
fi
```

## gh CLI installation

The `.claude/hooks/session-start.sh` hook automatically installs gh CLI on
CC web startup (downloads tarball, no apt-get needed).

## When to use CC web

- Quick tasks that don't need TexLive or Playwright
- Low-friction agent spawning
- Code review, Rust/Python work, git operations

## When NOT to use CC web

- LaTeX/PDF builds (use local)
- Literature search requiring JS websites (use local/codespace)
- Tasks requiring skills to work reliably (use local/codespace)
- Parallel agent work with worktrees (use local with catnip/codespace)
