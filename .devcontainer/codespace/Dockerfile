# -----------------------------------------------------------------------------
# Codespace devcontainer for msc-viterbo (GitHub Codespaces)
#
# WHY SEPARATE FROM LOCAL DOCKERFILE:
# Local and Codespace environments have different needs. Keeping them separate
# means editing one doesn't require thinking about effects on the other.
# Local has: sccache, more TeX packages, extra CLI tools (ctags, entr, etc.)
#
# Based on official sources:
# - Base: mcr.microsoft.com/devcontainers/base:ubuntu (has git, zsh, vscode user)
# - uv: copied from ghcr.io/astral-sh/uv (recommended by Astral)
# - Rust: rustup.rs (official)
# - Node: nodesource (well-tested)
# - TexLive: installed from Ubuntu repos for PDF builds
# -----------------------------------------------------------------------------

FROM mcr.microsoft.com/devcontainers/base:ubuntu

ENV DEBIAN_FRONTEND=noninteractive

# Build dependencies for Rust crates (ssl, etc)
RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    pkg-config \
    libssl-dev \
    python3 \
    python3-venv \
    && rm -rf /var/lib/apt/lists/*

# TexLive and LaTeXML (large layer, cached separately)
# Install minimal TexLive scheme + required packages for thesis builds
RUN apt-get update && apt-get install -y --no-install-recommends \
    texlive-latex-base \
    texlive-latex-extra \
    texlive-fonts-recommended \
    texlive-fonts-extra \
    texlive-science \
    latexmk \
    chktex \
    latexml \
    && rm -rf /var/lib/apt/lists/*

# CLI tools (gh is in Ubuntu repos)
RUN apt-get update && apt-get install -y --no-install-recommends \
    ripgrep \
    jq \
    gh \
    && rm -rf /var/lib/apt/lists/*

# Node.js 22.x via nodesource
# https://github.com/nodesource/distributions
RUN curl -fsSL https://deb.nodesource.com/setup_22.x | bash - \
    && apt-get install -y --no-install-recommends nodejs \
    && rm -rf /var/lib/apt/lists/*

# uv - copy from official Astral image (recommended approach)
# https://github.com/astral-sh/uv/blob/main/docs/guides/integration/docker.md
COPY --from=ghcr.io/astral-sh/uv:0.5.14 /uv /uvx /usr/local/bin/

# Switch to vscode user for Rust (toolchain installed per-user)
USER vscode
ENV HOME=/home/vscode
ENV PATH="$HOME/.cargo/bin:$PATH"

# Rust via rustup (official)
# https://rustup.rs/
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain stable \
    && . "$HOME/.cargo/env" \
    && rustup component add rustfmt clippy

WORKDIR /workspaces/msc-viterbo
