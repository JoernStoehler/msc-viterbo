# Claude Code Web Environment

CC Web has limitations compared to local CLI. This document covers known issues and workarounds.

## Environment Detection

The startup hook prints environment type:
```
Environment: CC Web (limited) — see docs/conventions/cc-web.md
```

## Known Limitations

### Git Proxy
CC Web uses a git proxy (`http://local_proxy@127.0.0.1:PORT/git/...`):
- `gh pr checks`, `gh issue list` fail (can't detect GitHub host)
- **Use `gh api` instead:** `gh api repos/OWNER/REPO/issues`
- Local git history may be shallow — use `gh api` for full commit history

### `claude -p` Not Working
As of Feb 2026, `claude -p --model haiku` produces no output. Workaround: defer tasks requiring subprocess Claude calls.

### Skills Not Auto-Loading
See #103. Skills may not load due to known Claude Code bugs. Workaround: manual skill references in prompts.

### Other Limitations
- **apt-get blocked** — DNS proxy architecture blocks package management
- **Playwright cannot install browsers** — Browser automation fails
- **No persistent storage** — Git worktrees cannot be used

## gh CLI Installation

The startup hook auto-installs gh CLI. If it fails:
```bash
wget -q "https://github.com/cli/cli/releases/download/v2.63.2/gh_2.63.2_linux_amd64.tar.gz" -O /tmp/gh.tar.gz
tar -xzf /tmp/gh.tar.gz -C /tmp
mkdir -p ~/.local/bin
cp /tmp/gh_2.63.2_linux_amd64/bin/gh ~/.local/bin/
export PATH="$HOME/.local/bin:$PATH"
```

## Startup Hook Crash Fixes

If CC Web won't start, the hook may be crashing. Common causes:

| Issue | Risk | Fix |
|-------|------|-----|
| `bash -lc` flag | HIGH | Use `bash -c` (no login shell) |
| `$CLAUDE_PROJECT_DIR` unset | HIGH | Use `${CLAUDE_PROJECT_DIR:-.}` fallback |
| `set -e` in hook | MEDIUM | Remove or add `|| true` to commands |
| `wget` timeout | MEDIUM | Add `--timeout=30` flag |

### Emergency: Minimal Settings
If CC Web won't start at all, use minimal settings with no hooks:
```json
{
  "env": { "GIT_PAGER": "cat" },
  "permissions": { "defaultMode": "bypassPermissions" }
}
```

### Testing Hook Manually
```bash
echo '{"source":"startup"}' | bash .claude/hooks/session-start.sh
```

## User Context

CC Web users are typically:
- On mobile (no local CLI available)
- Using GitHub.com GUI only
- Limited to what CC Web can do in-browser

## Feature Comparison

| Feature | Local | CC Web |
|---------|-------|--------|
| Git history | Full | Often shallow |
| `gh pr`/`gh issue` | Works | Use `gh api` |
| `claude -p` | Works | Broken |
| Skills | Auto-load | Manual |
| File system | Full | Sandboxed |
| apt-get | Works | Blocked |
