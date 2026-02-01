# Claude Code Web Environment

This document covers CC Web-specific limitations and workarounds.

## Environment Detection

The startup hook prints environment type:
```
Environment: CC Web (limited) — see docs/conventions/cc-web.md
```

## Known Limitations

### Git Proxy

CC Web uses a git proxy (`http://local_proxy@127.0.0.1:PORT/git/...`). This means:
- `gh pr checks`, `gh issue list` fail (can't detect GitHub host)
- Use `gh api` instead: `gh api repos/OWNER/REPO/issues`
- Local git history may be shallow — use `gh api` for full history

### `claude -p` Not Working

As of Feb 2026, `claude -p --model haiku` produces no output in CC Web. Workaround: defer tasks requiring subprocess Claude calls.

### gh CLI Installation

The startup hook auto-installs gh CLI. If it fails:
```bash
wget -q "https://github.com/cli/cli/releases/download/v2.63.2/gh_2.63.2_linux_amd64.tar.gz" -O /tmp/gh.tar.gz
tar -xzf /tmp/gh.tar.gz -C /tmp
mkdir -p ~/.local/bin
cp /tmp/gh_2.63.2_linux_amd64/bin/gh ~/.local/bin/
export PATH="$HOME/.local/bin:$PATH"
```

### Skills Not Auto-Loading

See #103. Skills may not load in CC Web due to known Claude Code bugs. Workaround: manual skill references in prompts.

## User Context

CC Web users are typically:
- On mobile (no local CLI available)
- Using GitHub.com GUI only
- Limited to what CC Web can do in-browser

## What's Different from Local

| Feature | Local | CC Web |
|---------|-------|--------|
| Git history | Full | Often shallow |
| `gh pr`/`gh issue` | Works | Use `gh api` |
| `claude -p` | Works | Broken |
| Skills | Auto-load | Manual |
| File system | Full | Sandboxed |
