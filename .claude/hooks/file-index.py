#!/usr/bin/env python3
"""
Generates a compact file index for agent context at session startup.

Uses bash-style brace expansion for compactness:
  dir/{a,b,c}.rs        # same extension
  dir/{a.rs,b.md}       # mixed extensions
  dir/                  # empty or dirs-only

Blacklist approach: shows everything except explicitly excluded patterns.
"""
from __future__ import annotations

import sys
from collections import defaultdict
from pathlib import Path
from types import SimpleNamespace

HELP = """\
Usage: file-index.py [--help]

Prints a compact file index using bash-style brace expansion.
Edit CONFIG in this script to adjust blacklist and display rules.
"""

CONFIG = SimpleNamespace(
    # Directories to completely skip (never show)
    # Criterion: Benefit < Cost
    # - Cost: tokens + cognitive load of processing
    # - Benefit: certainty of existence + exact location (vs searching/predicting)
    blacklist_dirs={
        ".git",
        ".venv",
        "target",
        "build",
        "dist",
        "node_modules",
        "__pycache__",  # predictable from .py files
        ".pytest_cache",  # predictable from pytest usage
        ".mypy_cache",  # predictable from mypy usage
        ".ruff_cache",  # predictable from ruff usage
        ".ipynb_checkpoints",  # predictable from .ipynb files
        ".latexmk",  # predictable from LaTeX build
        "site",  # predictable from Python
        "site-packages",  # predictable from Python
        "images",  # downloaded paper figures (paper .tex already shown)
    },
    # Prefixes for directories to skip
    blacklist_prefixes={"_minted"},  # LaTeX minted cache, predictable
    # File extensions to skip
    # Criterion: existence is redundant with other visible files
    blacklist_extensions={".pyc", ".pyo"},  # bytecode, inside already-hidden __pycache__
    # Safety limit for pathological repos only (this repo's max depth is ~10)
    depth_limit=50,
    # Directories with more than this many files get summarized
    file_summary_threshold=15,
)


def should_skip(path: Path, name: str) -> bool:
    """Check if a path should be skipped based on blacklist rules."""
    if name in CONFIG.blacklist_dirs:
        return True
    if any(name.startswith(pfx) for pfx in CONFIG.blacklist_prefixes):
        return True
    if path.is_file() and path.suffix in CONFIG.blacklist_extensions:
        return True
    return False


def compress_filenames(names: list[str]) -> str:
    """Compress a list of filenames using brace expansion.

    Examples:
        ['foo.rs', 'bar.rs', 'baz.rs'] -> '{bar,baz,foo}.rs'
        ['foo.rs', 'bar.md'] -> '{bar.md,foo.rs}'
        ['README.md'] -> 'README.md'

    All files in a directory are wrapped in braces when multiple, ensuring
    the path prefix applies to all: dir/{a.x,b.y} not dir/a.x b.y
    """
    if not names:
        return ""
    if len(names) == 1:
        return names[0]

    # Group by extension
    by_ext: dict[str, list[str]] = defaultdict(list)
    for name in names:
        if "." in name and not name.startswith("."):
            ext = name[name.rfind("."):]
            stem = name[:name.rfind(".")]
        else:
            ext = ""
            stem = name
        by_ext[ext].append(stem)

    # If all files share one extension, use {a,b,c}.ext
    if len(by_ext) == 1:
        ext, stems = next(iter(by_ext.items()))
        return f"{{{','.join(sorted(stems))}}}{ext}"

    # Mixed extensions: {a.x,b.y,c.z}
    all_files = sorted(names)
    return "{" + ",".join(all_files) + "}"


def collect_tree(root: Path, rel: Path, depth: int) -> list[tuple[str, list[str], int]]:
    """Collect directory entries recursively.

    Returns list of (dir_path, [filenames], omitted_count) tuples.
    """
    results: list[tuple[str, list[str], int]] = []
    abs_path = root / rel

    if not abs_path.is_dir():
        return results

    try:
        children = sorted(abs_path.iterdir(), key=lambda x: (not x.is_dir(), x.name.lower()))
    except PermissionError:
        return results

    files: list[str] = []
    subdirs: list[Path] = []

    for child in children:
        if child.is_symlink():
            continue
        if should_skip(child, child.name):
            continue

        if child.is_file():
            files.append(child.name)
        elif child.is_dir():
            subdirs.append(child)

    # Handle files in current directory
    dir_str = str(rel) if str(rel) != "." else "."
    omitted = 0

    if depth >= CONFIG.depth_limit:
        # At depth limit: count all files recursively and summarize
        total_files = len(files)
        for subdir in subdirs:
            try:
                total_files += sum(1 for p in subdir.rglob("*")
                                   if p.is_file() and not p.is_symlink()
                                   and not should_skip(p, p.name))
            except PermissionError:
                pass
        if total_files > 0:
            results.append((dir_str + "/", [], total_files))
        return results

    if files:
        if len(files) > CONFIG.file_summary_threshold:
            # Too many files: summarize ALL files (including subdirs) and don't recurse
            by_ext: dict[str, int] = defaultdict(int)
            for f in files:
                ext = Path(f).suffix or "(no ext)"
                by_ext[ext] += 1
            # Also count files in subdirs recursively
            for subdir in subdirs:
                try:
                    for p in subdir.rglob("*"):
                        if p.is_file() and not p.is_symlink() and not should_skip(p, p.name):
                            ext = p.suffix or "(no ext)"
                            by_ext[ext] += 1
                except PermissionError:
                    pass
            total = sum(by_ext.values())
            summary = ", ".join(f"{c}{e}" for e, c in sorted(by_ext.items(), key=lambda x: -x[1]))
            results.append((dir_str + "/", [f"<{total} files: {summary}>"], 0))
            return results  # Don't recurse into subdirs
        else:
            results.append((dir_str + "/", files, 0))
    elif not subdirs:
        # Empty directory
        results.append((dir_str + "/", ["(empty)"], 0))

    # Recurse into subdirectories
    for subdir in subdirs:
        child_rel = rel / subdir.name
        results.extend(collect_tree(root, child_rel, depth + 1))

    return results


def render_index(root: Path) -> list[str]:
    """Render the file index as compact lines."""
    entries = collect_tree(root, Path("."), 0)
    lines: list[str] = []

    for dir_path, files, omitted in entries:
        if omitted > 0:
            lines.append(f"{dir_path} ({omitted} files)")
        elif files:
            if files[0].startswith("<"):
                # Summary line
                lines.append(f"{dir_path} {files[0]}")
            elif files[0] == "(empty)":
                lines.append(f"{dir_path} (empty)")
            else:
                compressed = compress_filenames(files)
                # Clean up the path display
                if dir_path == "./":
                    lines.append(compressed)
                else:
                    # Remove leading ./ for cleaner output
                    clean_dir = dir_path[2:] if dir_path.startswith("./") else dir_path
                    lines.append(f"{clean_dir}{compressed}")

    return lines


def main() -> int:
    if len(sys.argv) > 1:
        if sys.argv[1] in ("--help", "-h"):
            print(HELP)
            return 0
        print(f"Unknown flag: {sys.argv[1]}", file=sys.stderr)
        return 1

    root = Path.cwd().resolve()

    print("[File Index] Repository structure (bash-style brace expansion)")
    print()
    for line in render_index(root):
        print(line)

    return 0


if __name__ == "__main__":
    sys.exit(main())
