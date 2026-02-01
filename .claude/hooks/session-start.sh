#!/bin/bash
# SessionStart hook:
# 1. Print compressed file index (all environments, startup only)
# 2. Install gh CLI in Claude Code web environments (silent)

# Read hook input from stdin
hook_input=$(cat)
source=$(echo "$hook_input" | jq -r '.source // "startup"' 2>/dev/null || echo "startup")

# Only run on startup (not resume/compact/clear)
[ "$source" != "startup" ] && exit 0

# --- Environment Detection ---
is_web_env=false
[ "$CLAUDE_CODE_REMOTE" = "true" ] && is_web_env=true
[ "${CLAUDE_ENVIRONMENT:-}" = "ccweb" ] && is_web_env=true
[ -n "${CODESPACES:-}" ] && is_web_env=true

if [ "$is_web_env" = "true" ]; then
    echo "Environment: CC Web (limited) — see docs/conventions/cc-web.md"
else
    echo "Environment: Local CLI"
fi
echo ""

# --- Shallow Clone Warning ---
if command -v git &>/dev/null && [ -d .git ]; then
    local_commits=$(git rev-list --count HEAD 2>/dev/null || echo "0")
    if [ "$local_commits" -lt 50 ]; then
        echo "WARNING: Shallow clone detected ($local_commits commits locally)."
        echo "         Use 'gh api' for full history, not local git log."
        echo ""
    fi
fi

# --- File Index (all environments) ---
# Print compressed repo structure so agent has file awareness in context
CLAUDE_PROJECT_DIR="${CLAUDE_PROJECT_DIR:-.}"
echo "=== Repository File Index ==="
echo "(Auto-generated to help navigate the codebase)"
echo ""
python3 "$CLAUDE_PROJECT_DIR/.claude/hooks/file-index.py" 2>/dev/null || echo "(file-index.py not available)"
echo ""
echo "=== End File Index ==="
echo ""

# --- gh CLI installation (web environment only) ---
[ "$is_web_env" = "false" ] && exit 0

# Skip if gh already installed
command -v gh &>/dev/null && exit 0

# Install gh CLI (silent unless errors)
(
    type -p wget >/dev/null || exit 1

    tmpdir=$(mktemp -d)
    trap 'rm -rf "$tmpdir"' EXIT

    wget --timeout=30 -q "https://github.com/cli/cli/releases/download/v2.63.2/gh_2.63.2_linux_amd64.tar.gz" -O "$tmpdir/gh.tar.gz" || exit 1
    tar -xzf "$tmpdir/gh.tar.gz" -C "$tmpdir" || exit 1

    mkdir -p "$HOME/.local/bin"
    cp "$tmpdir/gh_2.63.2_linux_amd64/bin/gh" "$HOME/.local/bin/" || exit 1
    chmod +x "$HOME/.local/bin/gh"
) 2>&1 | grep -i error >&2

# Add to PATH if needed
if [[ ":$PATH:" != *":$HOME/.local/bin:"* ]]; then
    export PATH="$HOME/.local/bin:$PATH"
    [ -n "$CLAUDE_ENV_FILE" ] && echo "export PATH=\"\$HOME/.local/bin:\$PATH\"" >> "$CLAUDE_ENV_FILE"
fi

# Verify (warn but don't block)
if ! "$HOME/.local/bin/gh" --version &>/dev/null; then
    echo "gh CLI installation failed (non-blocking)" >&2
fi

exit 0
