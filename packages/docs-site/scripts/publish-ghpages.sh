#!/usr/bin/env bash
set -euo pipefail

# Publish the staged docs-site/public/ to the gh-pages branch via a temporary worktree.
# Preconditions: packages/docs-site/scripts/stage-hub.sh has been run; public/ contains fresh artifacts.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DOCS_SITE_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
REPO_ROOT="$(cd "${DOCS_SITE_ROOT}/../.." && pwd)"
PUBLIC_DIR="${DOCS_SITE_ROOT}/public"
BRANCH="gh-pages"
WORKTREE_DIR="$(mktemp -d /tmp/docs-site-gh-pages.XXXXXX)"

if [ ! -d "${PUBLIC_DIR}" ]; then
  echo "ERROR: public/ not found; run stage-hub.sh first" >&2
  exit 1
fi

cd "${REPO_ROOT}"

if ! git show-ref --verify --quiet "refs/heads/${BRANCH}"; then
  echo "Creating ${BRANCH} branch"
  git branch "${BRANCH}" >/dev/null
fi

echo "Adding worktree at ${WORKTREE_DIR}"
git worktree add --force "${WORKTREE_DIR}" "${BRANCH}" >/dev/null

cleanup() {
  git worktree remove --force "${WORKTREE_DIR}" >/dev/null || true
  rm -rf "${WORKTREE_DIR}"
}
trap cleanup EXIT

echo "Clearing old contents"
rm -rf "${WORKTREE_DIR:?}"/*

echo "Copying public -> worktree"
cp -a "${PUBLIC_DIR}"/. "${WORKTREE_DIR}/"

cd "${WORKTREE_DIR}"
if [ -z "$(git status --porcelain)" ]; then
  echo "No changes to publish" >&2
  exit 0
fi

git add -A
commit_msg="docs: publish $(date -u +%Y-%m-%dT%H:%M:%SZ)"
git commit -m "${commit_msg}" >/dev/null

echo "Pushing ${BRANCH}"
git push origin "${BRANCH}"

echo "Published to ${BRANCH}. Worktree cleaned."
