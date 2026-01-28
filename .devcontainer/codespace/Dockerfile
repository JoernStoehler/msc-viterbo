FROM mcr.microsoft.com/devcontainers/base:ubuntu

ENV DEBIAN_FRONTEND=noninteractive

SHELL ["/bin/bash", "-lc"]

# -----------------------------------------------------------------------------
# Codespace devcontainer image for msc-viterbo
#
# Simplified version of local Dockerfile:
# - NO TexLive (use local devcontainer for PDF builds)
# - Same toolchain: Rust, Python, uv, Node.js
# -----------------------------------------------------------------------------

# Base system dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    git \
    git-lfs \
    build-essential \
    pkg-config \
    libssl-dev \
    python3 \
    python3-venv \
    python3-pip \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# CLI tools
RUN apt-get update && apt-get install -y --no-install-recommends \
    ripgrep \
    jq \
    gh \
    tree \
    && rm -rf /var/lib/apt/lists/*

# Node.js 22.x
RUN curl -fsSL https://deb.nodesource.com/setup_22.x | bash - \
    && apt-get update \
    && apt-get install -y --no-install-recommends nodejs \
    && rm -rf /var/lib/apt/lists/* \
    && node -v && npm -v

# uv (Python packaging)
ENV UV_INSTALL_DIR=/usr/local
ENV UV_VERSION=0.5.14
RUN curl -LsSf https://astral.sh/uv/${UV_VERSION}/install.sh | sh \
    && /usr/local/bin/uv --version

# Switch to dev user for Rust
USER vscode
ENV HOME=/home/vscode
ENV PATH="$HOME/.cargo/bin:$HOME/.local/bin:$PATH"

# Rust toolchain
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain stable \
    && "$HOME/.cargo/bin/rustup" component add rustfmt clippy

WORKDIR /workspaces/msc-viterbo
