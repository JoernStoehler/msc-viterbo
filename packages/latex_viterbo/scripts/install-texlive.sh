#!/usr/bin/env bash
set -euo pipefail

# install-texlive.sh: Install TexLive packages for thesis builds
#
# This script installs TexLive via apt-get for Ubuntu-based systems.
# Run this if pdflatex/latexmk commands are not available.
#
# Usage:
#   ./scripts/install-texlive.sh [--help]
#
# Installation time: ~2 minutes
# Disk usage: ~1.3GB after installation

usage() {
  cat <<'EOF'
Usage: scripts/install-texlive.sh [--help]

Installs TexLive packages needed to build the thesis via apt-get.

When to run this script:
  Run this if `pdflatex` is not found when trying to build LaTeX documents.
  The script checks if pdflatex is already available and exits if it is.

What this installs:
  - texlive-latex-base (core LaTeX)
  - texlive-latex-extra (additional packages like beamer)
  - texlive-fonts-recommended (standard fonts)
  - texlive-science (math/science packages)
  - texlive-bibtex-extra (bibliography support)
  - texlive-pictures (tikz and diagram packages)
  - latexmk (build automation)
  - chktex (linting support)

Note: This installs TexLive 2023 from Ubuntu apt repositories.

Installation details:
  Time: ~2 minutes
  Disk: ~1.3GB installed
EOF
}

if [[ "${1:-}" == "--help" || "${1:-}" == "-h" ]]; then
  usage
  exit 0
fi

# Check if already installed
if command -v pdflatex >/dev/null 2>&1; then
  echo "✓ TexLive already installed ($(pdflatex --version | head -n1))"
  exit 0
fi

echo "📚 Installing TexLive packages for thesis builds..."
echo "   This will take ~2 minutes and use ~1.3GB disk space."
echo ""

# Update package lists
echo "→ Updating apt package lists..."
sudo apt-get update -qq 2>&1 | grep -v "Reading" || true

# Install TexLive packages
echo "→ Installing TexLive packages..."
sudo apt-get install -y -qq \
  texlive-latex-base \
  texlive-latex-extra \
  texlive-fonts-recommended \
  texlive-science \
  texlive-bibtex-extra \
  texlive-pictures \
  latexmk \
  chktex 2>&1 | grep -E "(Setting up|Unpacking)" || true

echo ""
echo "✅ TexLive installation complete!"
echo ""
echo "Installed tools:"
pdflatex --version | head -n1
latexmk --version 2>&1 | head -n1
chktex --version 2>&1 | head -n1

echo ""
echo "You can now build the thesis:"
echo "  cd packages/latex_viterbo"
echo "  ./scripts/build.sh --pdf-only"
