#!/usr/bin/env bash
set -euo pipefail

# Build and (optionally) deploy the combined documentation site.
# This is a stub; package-specific docs build commands should be added
# in future GitHub issues and wired up here.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

echo "Building docs for msc-viterbo..."
echo "TODO: invoke per-package docs builders and aggregate into a gh-pages site."
