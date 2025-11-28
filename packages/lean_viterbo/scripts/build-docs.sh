#!/usr/bin/env bash
set -euo pipefail

# Lean docs build placeholder: fails fast until doc generation is configured.
# Intentionally exits non-zero so the pipeline reminds us to wire doc-gen.

echo "ERROR: Lean doc generation not configured. Add doc-gen (doc-gen4 / lake doc) and update this script." >&2
exit 1
