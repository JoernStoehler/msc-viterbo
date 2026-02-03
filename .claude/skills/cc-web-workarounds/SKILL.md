---
name: cc-web-workarounds
description: Claude Code Web environment limitations and workarounds. Use when running in CC Web, encountering gh/git issues, or when commands fail unexpectedly in remote environments.
---

[proposed]

# CC Web Workarounds

Limitations and workarounds for Claude Code Web environments.

## Environment Detection

```bash
is_web_env=false
[ "$CLAUDE_CODE_REMOTE" = "true" ] && is_web_env=true
[ "${CLAUDE_ENVIRONMENT:-}" = "ccweb" ] && is_web_env=true
[ -n "${CODESPACES:-}" ] && is_web_env=true
```

## Known Limitations

| Issue | Workaround |
|-------|-----------|
| `gh pr checks` fails | Use `gh api repos/OWNER/REPO/actions/runs` |
| `gh issue list` fails | Use `gh api repos/OWNER/REPO/issues` |
| Shallow git history (<50 commits) | Use `gh api` for full history |
| `claude -p` subprocess broken | Defer tasks needing Claude subprocess |
| apt-get blocked | None; use local devcontainer |
| No git worktrees | Single-branch workflow only |
| No TexLive/LaTeXML | Use local for thesis builds |

## GitHub CLI Workarounds

### Instead of `gh pr checks`:
```bash
gh api repos/{owner}/{repo}/commits/{sha}/check-runs --jq '.check_runs[] | {name, status, conclusion}'
```

### Instead of `gh issue list`:
```bash
gh api repos/{owner}/{repo}/issues --jq '.[] | {number, title, state}'
```

### Instead of local git log:
```bash
gh api repos/{owner}/{repo}/commits --jq '.[].commit.message'
```

## Shallow Clone Warning

Session startup detects shallow clones:
```bash
local_commits=$(git rev-list --count HEAD 2>/dev/null || echo "0")
if [ "$local_commits" -lt 50 ]; then
    echo "WARNING: Shallow clone detected"
fi
```

## Hook Crash Prevention

When writing hooks for CC Web:
- Use `bash -c` not `bash -lc` (no login shell)
- Fallback: `${CLAUDE_PROJECT_DIR:-.}`
- Add `|| true` with `set -e`
- Add `--timeout=30` to wget

## Emergency Minimal Settings

If hooks crash, use this `.claude/settings.json`:
```json
{
  "env": { "GIT_PAGER": "cat" },
  "permissions": { "defaultMode": "bypassPermissions" }
}
```

## See Also

- `.devcontainer/CLAUDE.md` — Environment overview
- `.claude/hooks/session-start.sh` — Environment detection
