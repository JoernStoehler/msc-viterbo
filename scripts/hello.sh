#!/usr/bin/env bash
set -euo pipefail

echo "[hello] pwd"
pwd

echo "[hello] git status -sb"
git status -sb || true

# show the file tree (compact, simple)
echo "[hello] compact tree"
printf '%s\n' "$PWD"

python3 - <<'PY'
from pathlib import Path

skip_names = {".git", ".venv", "build", "dist", "site-packages", "site", "target"}
skip_paths = {"packages/thesis"}
hide_names = {"__pycache__", ".mypy_cache", ".pytest_cache", ".ruff_cache"}

root = Path(".").resolve()


def is_skip(rel: Path) -> bool:
    rel_str = rel.as_posix()
    return rel.name in skip_names or rel_str in skip_paths


def list_children(rel: Path):
    base = root / rel
    children = []
    for p in sorted(base.iterdir(), key=lambda x: (not x.is_dir(), x.name.lower())):
        if p.name in hide_names:
            continue
        child_rel = rel / p.name
        skip = is_skip(child_rel)
        children.append((child_rel, p.is_dir(), skip))
    return children


def collapse(rel: Path):
    abs_path = root / rel
    if not abs_path.is_dir():
        return rel.name, rel
    parts = [rel.name]
    current = rel
    while True:
        if is_skip(current):
            break
        kids = list_children(current)
        dirs = [k for k in kids if k[1]]
        files = [k for k in kids if not k[1]]
        if files or len(dirs) != 1 or dirs[0][2]:
            break
        current = dirs[0][0]
        parts.append(current.name)
    return "/".join(parts) + "/", current


lines = []


def render(rel: Path, prefix: str, last: bool):
    abs_path = root / rel
    is_dir = abs_path.is_dir()
    label, end_rel = collapse(rel) if is_dir else (rel.name, rel)
    children = [] if (not is_dir or is_skip(end_rel)) else list_children(end_rel)
    empty = is_dir and not children and not is_skip(end_rel)
    suffix = " (skipped)" if is_skip(rel) else (" (empty)" if empty else "")
    connector = "└── " if last else "├── "
    lines.append(f"{prefix}{connector}{label}{suffix}")
    if not is_dir or is_skip(end_rel):
        return
    new_prefix = prefix + ("    " if last else "│   ")
    for idx, (child_rel, is_dir, skipped) in enumerate(children):
        render(child_rel, new_prefix, idx == len(children) - 1)


print(".")
top_children = list_children(Path("."))
for idx, (rel, is_dir, skipped) in enumerate(top_children):
    render(rel, "", idx == len(top_children) - 1)

print("\n".join([ln for ln in lines if ln.strip()]))
PY
