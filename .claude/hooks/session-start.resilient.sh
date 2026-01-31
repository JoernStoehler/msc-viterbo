#!/bin/bash
# SessionStart hook (RESILIENT VERSION for CC Web):
# 1. Print compressed file index (all environments, startup only)
# 2. Install gh CLI in Claude Code web environments (silent)
#
# Changes from original:
# - Removed 'set -e' to prevent premature exit
# - Added CLAUDE_PROJECT_DIR fallback
# - Added wget timeout
# - Made all sections independently failsafe

# Read hook input from stdin
hook_input=$(cat)
source=$(echo "$hook_input" | jq -r '.source // "startup"' 2>/dev/null || echo "startup")

# Only run on startup (not resume/compact/clear)
[ "$source" != "startup" ] && exit 0

# Set CLAUDE_PROJECT_DIR fallback
CLAUDE_PROJECT_DIR="${CLAUDE_PROJECT_DIR:-.}"

# --- File Index (all environments) ---
# Print compressed repo structure so agent has file awareness in context
echo "=== Session Startup: Repository File Index ==="
echo "(This index is auto-generated to help you navigate the codebase)"
echo ""

if [ -f "$CLAUDE_PROJECT_DIR/.claude/hooks/file-index.py" ]; then
    python3 "$CLAUDE_PROJECT_DIR/.claude/hooks/file-index.py" 2>/dev/null || echo "(file-index.py failed - continuing)"
else
    echo "(file-index.py not found at $CLAUDE_PROJECT_DIR/.claude/hooks/file-index.py)"
fi

echo ""
echo "=== End File Index ==="
echo ""

# --- gh CLI installation (web environment only) ---
# Detect web environment via multiple signals:
# - CLAUDE_CODE_REMOTE=true (CC Web)
# - CLAUDE_ENVIRONMENT=ccweb (CC Web alternative)
# - CODESPACES=true (GitHub Codespaces)
is_web_env=false
[ "$CLAUDE_CODE_REMOTE" = "true" ] && is_web_env=true
[ "${CLAUDE_ENVIRONMENT:-}" = "ccweb" ] && is_web_env=true
[ -n "${CODESPACES:-}" ] && is_web_env=true

[ "$is_web_env" = "false" ] && exit 0

# Skip if gh already installed
command -v gh &>/dev/null && exit 0

# Install gh CLI (silent unless errors)
(
    type -p wget >/dev/null || exit 1

    tmpdir=$(mktemp -d)
    trap 'rm -rf "$tmpdir"' EXIT

    # Add timeout to prevent hanging
    wget --timeout=30 -q "https://github.com/cli/cli/releases/download/v2.63.2/gh_2.63.2_linux_amd64.tar.gz" -O "$tmpdir/gh.tar.gz" || exit 1
    tar -xzf "$tmpdir/gh.tar.gz" -C "$tmpdir" || exit 1

    mkdir -p "$HOME/.local/bin"
    cp "$tmpdir/gh_2.63.2_linux_amd64/bin/gh" "$HOME/.local/bin/" || exit 1
    chmod +x "$HOME/.local/bin/gh" || exit 1
) 2>&1 | grep -i error >&2 || true  # Don't fail if grep finds nothing

# Add to PATH if needed
if [[ ":$PATH:" != *":$HOME/.local/bin:"* ]]; then
    export PATH="$HOME/.local/bin:$PATH"
    if [ -n "$CLAUDE_ENV_FILE" ] && [ -f "$CLAUDE_ENV_FILE" ]; then
        echo "export PATH=\"\$HOME/.local/bin:\$PATH\"" >> "$CLAUDE_ENV_FILE" 2>/dev/null || true
    fi
fi

# Verify (warn but don't block)
if ! "$HOME/.local/bin/gh" --version &>/dev/null; then
    echo "gh CLI installation failed (non-blocking)" >&2 || true
fi

exit 0
