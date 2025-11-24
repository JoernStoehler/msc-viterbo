#!/usr/bin/env bash
set -euo pipefail

# Fetch arXiv source tarballs (and optionally PDFs) into an immutable store
# and extract read-only copies into the current git worktree.
#
# Store (canonical, immutable):
#   ARXIV_STORE (env) or /workspaces/worktrees/shared/arxiv-store/<id>/vN/
#   contains: source.tar.gz, optional pdf, source.tar.gz.sha256
#
# Worktree extract (read-only, gitignored):
#   packages/thesis/build/arxiv/<id>/vN/
#
# Usage: packages/thesis/scripts/arxiv_fetch.sh [-s STORE_DIR] [-p] ID|URL [...]
#   -s STORE_DIR  Override canonical store path (default: ARXIV_STORE or /workspaces/worktrees/shared/arxiv-store)
#   -p            Also download PDF into store and extract alongside sources
#   -h            Help

usage() {
  cat <<'USAGE'
Usage: arxiv_fetch.sh [-s STORE_DIR] [-p] ID|URL [...]
  -s STORE_DIR  Canonical immutable store (default: ARXIV_STORE or /workspaces/worktrees/shared/arxiv-store)
  -p            Also download the compiled PDF
  -h            Show this help
Examples:
  packages/thesis/scripts/arxiv_fetch.sh 2405.16513v2
  ARXIV_STORE=/workspaces/worktrees/shared/arxiv-store packages/thesis/scripts/arxiv_fetch.sh -p 2008.10111v1
USAGE
}

repo_root=$(git -C "$(dirname "$0")/.." rev-parse --show-toplevel 2>/dev/null || true)
store_override=${ARXIV_STORE:-}
store_dir=""
download_pdf=false

while getopts "s:ph" opt; do
  case "${opt}" in
    s) store_dir="$OPTARG" ;;
    p) download_pdf=true ;;
    h) usage; exit 0 ;;
    *) usage; exit 1 ;;
  esac
done
shift $((OPTIND - 1))

if [ "$#" -eq 0 ]; then
  usage
  exit 1
fi

if [ -z "$store_dir" ]; then
  if [ -n "$store_override" ]; then
    store_dir="$store_override"
  else
    store_dir="/workspaces/worktrees/shared/arxiv-store"
  fi
fi

if [ -z "$repo_root" ] || [ ! -d "$repo_root/packages/thesis" ]; then
  echo "[error] must run inside repo to place worktree extracts" >&2
  exit 1
fi

worktree_extract_base="$repo_root/packages/thesis/build/arxiv"
mkdir -p "$store_dir" "$worktree_extract_base"
echo "[info] store: $store_dir"
echo "[info] extract base: $worktree_extract_base"

normalize_id() {
  local raw="$1"
  raw=${raw#https://arxiv.org/}
  raw=${raw#http://arxiv.org/}
  raw=${raw#abs/}
  raw=${raw#pdf/}
  raw=${raw#e-print/}
  raw=${raw%.pdf}
  raw=${raw%.tar.gz}
  raw=${raw%.gz}
  raw=${raw#/}
  if [[ -z "$raw" ]]; then
    return 1
  fi
  printf '%s' "$raw"
}

extract_version() {
  local id="$1"
  if [[ "$id" =~ v[0-9]+$ ]]; then
    echo "${id##*v}"
  else
    echo ""
  fi
}

sha_file() { echo "$1.sha256"; }

ensure_sha() {
  local file="$1"
  local sha_path
  sha_path=$(sha_file "$file")
  if [ ! -s "$sha_path" ]; then
    sha256sum "$file" >"$sha_path"
  fi
}

verify_sha() {
  local file="$1"
  local sha_path
  sha_path=$(sha_file "$file")
  sha256sum -c "$sha_path" >/dev/null
}

read_only() {
  chmod -R a-w "$@"
}

for arg in "$@"; do
  id=$(normalize_id "$arg") || { echo "[skip] could not parse arXiv id from '$arg'" >&2; continue; }
  version=$(extract_version "$id")
  if [ -z "$version" ]; then
    echo "[error] id '$id' has no explicit version (e.g., v1). Please specify one." >&2
    continue
  fi

  store_paper_dir="$store_dir/$id"
  mkdir -p "$store_paper_dir"
  src_tar="$store_paper_dir/source.tar.gz"

  if [ ! -s "$src_tar" ]; then
    echo "[fetch] $id → $src_tar"
    curl -L --fail "https://arxiv.org/e-print/$id" -o "$src_tar"
    ensure_sha "$src_tar"
    read_only "$src_tar" "$(sha_file "$src_tar")"
  else
    verify_sha "$src_tar"
    echo "[cached] $src_tar"
  fi

  if $download_pdf; then
    pdf_path="$store_paper_dir/${id}.pdf"
    if [ ! -s "$pdf_path" ]; then
      echo "[fetch] $id → $pdf_path"
      curl -L --fail "https://arxiv.org/pdf/$id.pdf" -o "$pdf_path"
      ensure_sha "$pdf_path"
      read_only "$pdf_path" "$(sha_file "$pdf_path")"
    else
      verify_sha "$pdf_path"
      echo "[cached] $pdf_path"
    fi
  fi

  read_only "$store_paper_dir"

  extract_dir="$worktree_extract_base/$id"
  mkdir -p "$extract_dir"
  tar -xzf "$src_tar" -C "$extract_dir"
  if $download_pdf; then
    cp "$pdf_path" "$extract_dir/"
    cp "$(sha_file "$pdf_path")" "$extract_dir/"
  fi
  read_only "$extract_dir"
  echo "[ready] extracted to $extract_dir"
done
