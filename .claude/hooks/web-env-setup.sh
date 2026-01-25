#!/bin/bash
# Hook: Install gh CLI in Claude Code web environments
# Only runs on startup in web environment, silent unless errors occur

# Read hook input from stdin (SessionStart provides JSON with source field)
hook_input=$(cat)
source=$(echo "$hook_input" | jq -r '.source // "startup"')

# Exit early if not in web environment
[ "$CLAUDE_CODE_REMOTE" != "true" ] && exit 0

# Only install on startup (not resume/compact/clear - gh persists in VM)
[ "$source" != "startup" ] && exit 0

# Exit early if gh is already installed
command -v gh &>/dev/null && exit 0

# Install gh CLI (suppress stdout, show stderr on failure)
# Using the official GitHub CLI installation method for Linux
(
    type -p wget >/dev/null || exit 1

    # Create temp dir for installation
    tmpdir=$(mktemp -d)
    trap 'rm -rf "$tmpdir"' EXIT

    # Download and install gh
    wget -q "https://github.com/cli/cli/releases/download/v2.63.2/gh_2.63.2_linux_amd64.tar.gz" -O "$tmpdir/gh.tar.gz" || exit 1
    tar -xzf "$tmpdir/gh.tar.gz" -C "$tmpdir" || exit 1

    # Install to user's local bin (no sudo needed)
    mkdir -p "$HOME/.local/bin"
    cp "$tmpdir/gh_2.63.2_linux_amd64/bin/gh" "$HOME/.local/bin/" || exit 1
    chmod +x "$HOME/.local/bin/gh"
) 2>&1 | grep -i error >&2

# Add to PATH if not already there
if [[ ":$PATH:" != *":$HOME/.local/bin:"* ]]; then
    export PATH="$HOME/.local/bin:$PATH"
    # Persist for the session if CLAUDE_ENV_FILE is available
    if [ -n "$CLAUDE_ENV_FILE" ]; then
        echo "export PATH=\"\$HOME/.local/bin:\$PATH\"" >> "$CLAUDE_ENV_FILE"
    fi
fi

# Verify installation succeeded (warn but don't block session)
if ! "$HOME/.local/bin/gh" --version &>/dev/null; then
    echo "gh CLI installation failed (non-blocking)" >&2
fi

exit 0
