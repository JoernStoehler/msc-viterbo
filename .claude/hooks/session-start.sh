#!/bin/bash
# SessionStart hook: install gh CLI in web environments (silent)

set -e

# Read hook input from stdin (SessionStart provides JSON with source field)
hook_input=$(cat)
source=$(echo "$hook_input" | jq -r '.source // "startup"')

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# web-env-setup: only on startup (gh persists in VM)
if [ "$source" = "startup" ]; then
    echo "$hook_input" | "$SCRIPT_DIR/web-env-setup.sh" || true
fi
