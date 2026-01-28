# -----------------------------------------------------------------------------
# Devcontainer image for msc-viterbo (local development variant)
#
# Layer ordering strategy for development iteration speed:
#   1. Base + system packages (very stable)
#   2. TeX packages (huge ~2.5GB, very stable) - cache this!
#   3. CLI tools (stable)
#   4. VS Code tunnel CLI (stable)
#   5. Node.js (stable)
#   6. uv (version may change)
#   7. Rust toolchain + sccache (components may change)
#
# Differences from codespace/:
# - Includes VS Code tunnel CLI for remote access
# - Includes sccache for faster Rust rebuilds (with persistent cache)
# - Designed for bind mounts from host
# -----------------------------------------------------------------------------

# Pin base image for reproducibility. Check for updates periodically:
# https://mcr.microsoft.com/v2/devcontainers/base/tags/list
FROM mcr.microsoft.com/devcontainers/base:1-ubuntu-24.04

ENV DEBIAN_FRONTEND=noninteractive

# Layer 1: Base system dependencies (rarely change)
RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    ca-certificates \
    curl \
    git \
    git-lfs \
    libssl-dev \
    pkg-config \
    python3 \
    python3-pip \
    python3-venv \
    && rm -rf /var/lib/apt/lists/*

# Layer 2: TeX toolchain (~2.5GB installed, very stable - cache this!)
# TexLive 2023 from Ubuntu apt repositories.
RUN apt-get update && apt-get install -y --no-install-recommends \
    biber \
    chktex \
    ghostscript \
    imagemagick \
    lacheck \
    latexml \
    latexmk \
    python3-pygments \
    texlive-bibtex-extra \
    texlive-extra-utils \
    texlive-fonts-extra \
    texlive-fonts-recommended \
    texlive-latex-extra \
    texlive-latex-recommended \
    texlive-luatex \
    texlive-pictures \
    texlive-science \
    texlive-xetex \
    && rm -rf /var/lib/apt/lists/*

# Layer 3: CLI tools used by agents (stable)
RUN apt-get update && apt-get install -y --no-install-recommends \
    entr \
    gh \
    inotify-tools \
    jq \
    ripgrep \
    tree \
    universal-ctags \
    && rm -rf /var/lib/apt/lists/*

# Layer 4: VS Code tunnel CLI (local-only, for remote access)
RUN set -eux; \
    tmpdir="$(mktemp -d)"; \
    curl -fsSL "https://update.code.visualstudio.com/latest/cli-linux-x64/stable" -o "$tmpdir/vscode-cli.tar.gz"; \
    tar -xzf "$tmpdir/vscode-cli.tar.gz" -C "$tmpdir"; \
    install -m 0755 "$tmpdir/code" /usr/local/bin/code-tunnel; \
    rm -rf "$tmpdir"

# Layer 5: Node.js 22.x (stable, version might bump occasionally)
RUN curl -fsSL https://deb.nodesource.com/setup_22.x | bash - \
    && apt-get install -y --no-install-recommends nodejs \
    && rm -rf /var/lib/apt/lists/* \
    && node -v && npm -v

# Layer 6: uv (Python packaging/runner) - version changes more often
# Note: maturin requires uv >= 0.4.25 for editable installs
ARG UV_VERSION=0.5.14
ENV UV_INSTALL_DIR=/usr/local
RUN curl -LsSf https://astral.sh/uv/${UV_VERSION}/install.sh | sh \
    && /usr/local/bin/uv --version

# Switch to non-root user for remaining installs
USER vscode
ENV HOME=/home/vscode
ENV PATH="$HOME/.cargo/bin:$HOME/.local/bin:$PATH"

# Layer 7: Rust toolchain + sccache (components may change during development)
# sccache provides faster rebuilds with persistent cache on local
ARG RUST_TOOLCHAIN=stable
RUN curl -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain ${RUST_TOOLCHAIN} \
    && rustup component add rustfmt clippy \
    && cargo install sccache \
    && rustc --version && cargo --version && sccache --version

WORKDIR /workspaces/msc-viterbo
