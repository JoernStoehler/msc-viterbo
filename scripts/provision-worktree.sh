#!/usr/bin/env bash
set -euo pipefail

# Provision a new git worktree for a single task or experiment.
#
# Usage:
#   scripts/provision-worktree.sh <worktree-name>
#
# This script:
#   - Creates a new branch "agentx/<worktree-name>" from origin/main (or main).
#   - Adds a git worktree under /var/tmp/msc-viterbo/worktrees/<worktree-name>.
#   - Ensures the /workspaces/worktrees symlink exists inside the devcontainer.
#   - Invokes scripts/worktree-post-add.sh so every new worktree gets the same
#     bootstrap steps (uv sync, future package hooks, etc.).

if [[ $# -ne 1 ]]; then
  echo "Usage: $0 <worktree-name>" >&2
  exit 1
fi

WORKTREE_NAME="$1"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKTREES_DIR="/var/tmp/msc-viterbo/worktrees"

mkdir -p "${WORKTREES_DIR}"

BRANCH_NAME="agentx/${WORKTREE_NAME}"
WORKTREE_PATH="${WORKTREES_DIR}/${WORKTREE_NAME}"

cd "${REPO_ROOT}"

if git show-ref --verify --quiet "refs/heads/${BRANCH_NAME}"; then
  echo "Branch ${BRANCH_NAME} already exists."
else
  if git show-ref --verify --quiet "refs/remotes/origin/main"; then
    git branch "${BRANCH_NAME}" origin/main
  else
    git branch "${BRANCH_NAME}" main
  fi
fi

if [[ -d "${WORKTREE_PATH}" ]]; then
  echo "Worktree directory already exists at ${WORKTREE_PATH}."
else
  git worktree add "${WORKTREE_PATH}" "${BRANCH_NAME}"
fi

if [[ ! -L "/workspaces/worktrees" ]]; then
  ln -s "${WORKTREES_DIR}" "/workspaces/worktrees"
fi

# Run shared post-add hook (best-effort, but fail if it exists and errors).
POST_ADD="${REPO_ROOT}/scripts/worktree-post-add.sh"
if [[ -x "${POST_ADD}" ]]; then
  "${POST_ADD}" "${WORKTREE_PATH}"
else
  echo "Skipping post-add hook; ${POST_ADD} not executable."
fi

echo "Provisioned worktree ${WORKTREE_NAME} at ${WORKTREE_PATH} on branch ${BRANCH_NAME}."
