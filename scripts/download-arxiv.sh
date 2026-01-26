#!/usr/bin/env bash
# Download arXiv paper TeX sources for agent reading
#
# Usage: scripts/download-arxiv.sh <arxiv-id> <folder-name>
# Example: scripts/download-arxiv.sh 2203.02043 Rudolf2022-worm-problem
#
# Folder naming convention:
#   Single author:  Surname + Year + description  (e.g., Rudolf2022-worm-problem)
#   Multi author:   Initials + Year + description (e.g., HK2024-counterexample)
#
# After running, remember to:
#   1. Update docs/papers/README.md with the new entry
#   2. Add BibTeX entry to packages/latex_viterbo/references.bib

set -euo pipefail

if [[ $# -lt 2 ]]; then
    echo "Usage: $0 <arxiv-id> <folder-name>"
    echo "Example: $0 2203.02043 Rudolf2022-worm-problem"
    exit 1
fi

ARXIV_ID="$1"
FOLDER_NAME="$2"
PAPERS_DIR="docs/papers"
TARGET_DIR="${PAPERS_DIR}/${FOLDER_NAME}"

# Check if folder already exists
if [[ -d "$TARGET_DIR" ]]; then
    echo "Error: $TARGET_DIR already exists"
    exit 1
fi

# Create folder and download
mkdir -p "$TARGET_DIR"
cd "$TARGET_DIR"

echo "Downloading arXiv:${ARXIV_ID}..."
wget -q "https://arxiv.org/e-print/${ARXIV_ID}" -O source

# Detect format and extract
if tar -tzf source >/dev/null 2>&1; then
    echo "Extracting tar.gz archive..."
    tar -xzf source
    rm source
else
    # Single gzip'd .tex file
    echo "Extracting gzip'd .tex file..."
    gunzip -c source > paper.tex
    rm source
fi

echo ""
echo "Downloaded to: $TARGET_DIR"
ls -la
echo ""
echo "Next steps:"
echo "  1. Update docs/papers/README.md"
echo "  2. Add BibTeX to packages/latex_viterbo/references.bib"
echo "  3. Websearch 'arXiv ${ARXIV_ID}' for title/authors if needed"
