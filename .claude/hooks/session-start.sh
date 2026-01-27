#!/bin/bash
# SessionStart hook wrapper - runs appropriate scripts based on source
# Combines web-env-setup.sh and repo-map.sh into one hook to avoid duplicate UI messages

set -e

# Read hook input from stdin (SessionStart provides JSON with source field)
hook_input=$(cat)
source=$(echo "$hook_input" | jq -r '.source // "startup"')

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"

# web-env-setup: only on startup (gh persists in VM)
if [ "$source" = "startup" ]; then
    echo "$hook_input" | "$SCRIPT_DIR/web-env-setup.sh" || true
fi

# repo-map.sh: on startup/compact/clear (skip resume - agent still has context)
if [ "$source" != "resume" ]; then
    "$PROJECT_DIR/scripts/repo-map.sh" || true
fi
