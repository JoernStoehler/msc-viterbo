FROM mcr.microsoft.com/devcontainers/base:ubuntu

ENV DEBIAN_FRONTEND=noninteractive

SHELL ["/bin/bash", "-lc"]

# -----------------------------------------------------------------------------
# Devcontainer image for msc-viterbo
#
# Design goals:
# - Keep the image simple and close to standard devcontainer patterns (KISS).
# - Install heavyweight, rarely changing dependencies in earlier layers so they
#   are cached across rebuilds.
# - Install more frequently tweaked tools (Node/npm, uv) after base deps.
# - Install language toolchains (Rust, Lean) once for the dev user here rather
#   than in postCreate, so they are baked into the image.
# -----------------------------------------------------------------------------

# Base system dependencies (rarely change; heavy but shared by all tools)
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    git \
    build-essential \
    pkg-config \
    libssl-dev \
    python3 \
    python3-venv \
    python3-pip \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# Common CLI tools used by agents (cheap to adjust; comes after base deps)
RUN apt-get update && apt-get install -y --no-install-recommends \
    ripgrep \
    jq \
    gh \
    universal-ctags \
    tree \
    && rm -rf /var/lib/apt/lists/*

# Node.js 22.x (npm included) for Codex CLI and other JS tooling.
# We keep this in the image so that npm is always available for postCreate
# steps (e.g. updating @openai/codex) without re-downloading Node on each run.
RUN curl -fsSL https://deb.nodesource.com/setup_22.x | bash - \
    && apt-get update \
    && apt-get install -y --no-install-recommends nodejs \
    && rm -rf /var/lib/apt/lists/* \
    && node -v && npm -v

# Install uv (Python packaging/runner) globally.
# uv is used as the canonical way to manage Python environments and deps.
ENV UV_INSTALL_DIR=/usr/local/bin
RUN curl -LsSf https://astral.sh/uv/install.sh | sh \
    && uv --version

# Switch to dev user for language toolchains.
# Toolchains live in the dev user's HOME so that cargo/elan behave normally.
USER vscode
ENV HOME=/home/vscode
ENV PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$HOME/.local/bin:$PATH"

# Install Rust (rustup + basic components).
# We install rustfmt/clippy up front so agents can rely on them everywhere.
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain stable \
    && "$HOME/.cargo/bin/rustup" component add rustfmt clippy || true

# Install Lean4 toolchain manager (elan).
# The specific toolchain is controlled by the lean_viterbo/lean-toolchain file
# and can be refined later via elan configuration.
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
    | bash -s -- -y \
    && "$HOME/.elan/bin/elan" --version || true

WORKDIR /workspaces/msc-viterbo
