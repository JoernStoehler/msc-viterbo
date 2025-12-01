# Maintain Environment

- Sources:
  - `.devcontainer/Dockerfile`
  - `.devcontainer/devcontainer.json`
  - `scripts/devcontainer-post-create.sh`
  - `msc-viterbo.code-workspace`
  - `scripts/worktree-prepare.sh`
- Goal: we want a single, reproducible, defined environment for all agents to operate in, with pinned versions and caches and installed convenience tools.
- The devcontainer is run on a single ubuntu host owned by the project owner. No other devices or clones participate in the thesis project. Shared caches are indeed shared with everyone.
- The sources define the entire environment. We don't accept local-only installs or changes that are not codified in the sources.
- The image is based on `mcr.microsoft.com/vscode/devcontainers/base:ubuntu`. It installs the toolchains we mentioned in `AGENTS.md`, and sets up shared caches mentioned in `agent_docs/maintain-environment-caches.md`.
- The workspace file defines recommended extensions and settings for VSCode, which is relevant mostly for the project owner and not the agents.
- For git worktrees, we always run teh prep script to initialize the toolchains and caches for the new worktree's packages.
