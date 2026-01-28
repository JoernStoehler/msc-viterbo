FROM mcr.microsoft.com/devcontainers/base:ubuntu

ENV DEBIAN_FRONTEND=noninteractive

SHELL ["/bin/bash", "-lc"]

# -----------------------------------------------------------------------------
# Devcontainer image for msc-viterbo (GitHub Codespaces variant)
#
# Differences from local/:
# - No TexLive (~2GB saved, faster startup)
# - No VS Code tunnel CLI (Codespaces has native tunnel)
# - Catnip handles git worktrees (no /workspaces/worktrees mount)
#
# TexLive omission means: LaTeX/PDF builds require local devcontainer.
# This is acceptable because thesis PDF builds are Jörn's task, not agents'.
# -----------------------------------------------------------------------------

# Base system dependencies (rarely change; heavy but shared by all tools).
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

# Common CLI tools used by agents
RUN apt-get update && apt-get install -y --no-install-recommends \
    ripgrep \
    jq \
    gh \
    universal-ctags \
    tree \
    inotify-tools \
    entr \
    && rm -rf /var/lib/apt/lists/*

# Node.js 22.x (npm included) for JS tooling.
RUN curl -fsSL https://deb.nodesource.com/setup_22.x | bash - \
    && apt-get update \
    && apt-get install -y --no-install-recommends nodejs \
    && rm -rf /var/lib/apt/lists/* \
    && node -v && npm -v

# Install uv (Python packaging/runner) globally. Pin for reproducibility.
ENV UV_INSTALL_DIR=/usr/local
ENV UV_VERSION=0.4.20
RUN curl -LsSf https://astral.sh/uv/${UV_VERSION}/install.sh | sh \
    && uv --version

# Switch to dev user for language toolchains.
USER vscode
ENV HOME=/home/vscode
ENV PATH="$HOME/.cargo/bin:$HOME/.local/bin:$PATH"

# Install Rust (rustup + basic components).
# sccache skipped: no persistent cache in Codespaces anyway.
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain stable \
    && "$HOME/.cargo/bin/rustup" component add rustfmt clippy || true

WORKDIR /workspaces/msc-viterbo
