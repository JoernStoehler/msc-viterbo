#!/bin/bash
# SessionStart hook - DISABLED FOR DEBUGGING
# All functionality removed to isolate CC crash cause
# To re-enable features, see git history for original implementation

# Minimal no-op hook: consume stdin, exit cleanly
cat > /dev/null
exit 0
