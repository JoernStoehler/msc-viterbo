#!/usr/bin/env python3
"""
Generates a compact file index for agent context at session startup.

WHY THIS EXISTS:
Agents benefit from knowing what files exist in a repo at session start.
Without this, they waste tokens searching/guessing file locations.
But listing ALL files wastes tokens on generated/cached content.

APPROACH:
1. Start with ALL files in the repo
2. Remove files/folders matching blacklist patterns
3. Compress remaining tree using bash-style brace expansion

WHY BLACKLIST (not whitelist):
- Whitelisting requires knowing all source file patterns in advance
- Blacklisting is safer: new source files are shown by default
- Only predictable generated/cached content is hidden

OUTPUT FORMAT (bash-style brace expansion):
  dir/{a,b,c}.rs        # same extension
  dir/{a.rs,b.md}       # mixed extensions
  dir/ (empty)          # folder exists but contents hidden/empty

COST-BENEFIT FRAMEWORK:
- Cost of showing a file: tokens + cognitive load
- Benefit of showing a file: certainty of existence + location
- Blacklist when: existence is 100% predictable from other files
  (e.g., __pycache__/ exists if .py files exist)
"""
from __future__ import annotations

import fnmatch
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
    # === BLACKLIST (gitignore-style patterns) ===
    #
    # Goal: Hide files/folders whose existence provides no useful information.
    # Criterion: "existence is predictable from other visible files"
    #
    # Pattern syntax (matches gitignore semantics):
    # - Pattern WITHOUT '/': matches NAME anywhere in tree
    #   e.g., "__pycache__" matches "foo/bar/__pycache__"
    # - Pattern WITH '/': matches against RELATIVE PATH from root
    #   e.g., "docs/papers/*/images" matches "docs/papers/foo/images"
    #
    # Broad vs specific patterns:
    # - Broad patterns (no '/') are DANGEROUS - they match anywhere
    #   Only use when the name is TOOL-ENFORCED (no false positives possible)
    # - Specific patterns (with '/') are SAFE - explicit paths
    #   Use for generic names like "target", "venv", "build"
    #
    # Folder existence vs contents:
    # - "foo" hides the folder entirely (existence hidden)
    # - "foo/*" hides contents but shows folder exists as "foo/ (empty)"
    #   Use when folder existence has information value (e.g., "build ran")
    #
    blacklist_patterns=[
        # === Broad patterns (justified: tool-enforced naming, no false positives) ===
        ".git",              # Only Git creates .git/
        "__pycache__",       # Only Python creates __pycache__/
        "*.pyc",             # Only Python creates .pyc files
        "*.pyo",             # Only Python creates .pyo files
        ".pytest_cache",     # Only pytest creates .pytest_cache/
        ".mypy_cache",       # Only mypy creates .mypy_cache/
        ".ruff_cache",       # Only ruff creates .ruff_cache/
        ".tox",              # Only tox creates .tox/
        ".ipynb_checkpoints",  # Only Jupyter creates .ipynb_checkpoints/
        "node_modules",      # Only npm/yarn creates node_modules/
        # LaTeX intermediate files (tool-enforced extensions, only LaTeX creates these)
        "*.aux",
        "*.fls",
        "*.fdb_latexmk",
        "*.blg",
        "*.bbl",
        "*.toc",
        "*.synctex.gz",
        "LaTeXML.cache",

        # === Specific paths (cautious: generic names could have false positives) ===
        # Pattern ends with /* to show folder existence but hide contents
        "experiments/.venv/*",
        "crates/target/*",
        # LaTeX caches (existence not valuable)
        "thesis/.latexmk",
        "thesis/talk-clarke-duality/.latexmk",
        "thesis/_minted-*",
        "thesis/talk-clarke-duality/_minted-*",
        # LaTeX build intermediates (generic extensions in specific paths)
        "thesis/build/*.log",
        "thesis/build/*.out",
        "thesis/build/lint/*.log",
        "thesis/build/lint/*.out",
        # Build assets are copies of source assets (predictable)
        "thesis/build/html/*.css",
        "thesis/build/html/assets/*",
        "thesis/build/lint/html/*.css",
        "thesis/build/lint/html/assets/*",
        # Paper figures
        "docs/papers/*/images",
        # LaTeXML bindings (dir existence valuable, individual files predictable from packages used)
        "thesis/assets/latexml/ar5iv-bindings/bindings/*",
        "thesis/assets/latexml/ar5iv-bindings/originals/*",
        "thesis/assets/latexml/ar5iv-bindings/supported_originals/*",
        "thesis/assets/latexml/ar5iv-bindings/deprecated/*",
        # Data outputs (generated, gitignored)
        "data/*",
    ],

    # Safety fallback for pathological repos with extreme nesting.
    # This repo's max depth is ~10, so 50 is just defensive.
    depth_limit=50,

    # === TREE PREFIXES (for long repeated prefixes) ===
    #
    # When multiple entries share a long prefix, use tree format:
    #   packages/python_viterbo/src/viterbo/experiments/
    #   | algorithm_comparison/{...}
    #   | benchmark_hk2017/{...}
    #
    # Cost-benefit:
    # - Fixed cost: cognitive complexity of understanding tree syntax
    # - Per-child cost: "| " prefix on each line (2 chars)
    # - Savings: not repeating prefix on each child
    #
    # Only worthwhile for LONG prefixes with MANY children.
    # Short prefixes or few children: fixed complexity cost dominates.
    #
    # These are hardcoded because they rarely change.
    tree_prefixes=[
        # Nested prefixes work because we use "longest match" logic
        "experiments/",
        "crates/",
        "thesis/",
        "docs/papers/",
    ],
)


def should_skip(rel_path: Path) -> bool:
    """Check if a path should be hidden based on blacklist patterns.

    WHY GITIGNORE-STYLE:
    - Well-known syntax, agents understand it
    - Distinguishes "match anywhere" vs "match specific path"

    PATTERN RULES:
    - No '/': matches NAME anywhere (e.g., "__pycache__" matches "a/b/__pycache__")
    - Has '/': matches full RELATIVE PATH (e.g., "a/*/c" matches "a/foo/c")

    WHY THIS MATTERS:
    - Broad patterns (no '/') are dangerous - could hide unintended files
    - Only use broad patterns for tool-enforced names (no false positives)
    - Use specific patterns (with '/') for generic names like "target", "build"
    """
    name = rel_path.name
    rel_str = str(rel_path)

    for pattern in CONFIG.blacklist_patterns:
        if "/" not in pattern:
            # No slash: match name anywhere
            if fnmatch.fnmatch(name, pattern):
                return True
        else:
            # Has slash: match full path
            if fnmatch.fnmatch(rel_str, pattern):
                return True
    return False


def compress_filenames(names: list[str]) -> str:
    """Compress a list of filenames using bash-style brace expansion.

    EXAMPLES:
        ['foo.rs', 'bar.rs'] -> '{bar.rs,foo.rs}'
        ['README.md'] -> '{README.md}'
        ['a.rs', 'b/', 'c.md'] -> '{a.rs,b/,c.md}'

    Always uses braces for clarity (distinguishes contents from path).
    """
    if not names:
        return ""
    return "{" + ",".join(sorted(names)) + "}"


def collect_tree(root: Path, rel: Path, depth: int) -> list[tuple[str, list[str]]]:
    """Recursively collect non-blacklisted files grouped by directory.

    WHY THIS STRUCTURE:
    - Groups files by directory for efficient brace expansion
    - Returns flat list (not nested tree) for simple rendering
    - Each tuple: (directory_path, [filenames_in_that_dir])

    WHY DEPTH LIMIT:
    - Safety fallback for pathological repos with extreme nesting
    - At limit: stop recursing, show remaining subdirs as "name/"
    - This repo's max depth is ~10, limit of 50 is defensive

    WHY "(empty)" FOR EMPTY DIRS:
    - Shows folder EXISTS even when contents are hidden/empty
    - Important for folders like ".venv/" and "target/" where
      existence confirms "env set up" or "build ran"
    """
    results: list[tuple[str, list[str]]] = []
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

        child_rel = rel / child.name
        if should_skip(child_rel):
            continue

        if child.is_file():
            files.append(child.name)
        elif child.is_dir():
            subdirs.append(child)

    # Handle depth limit (safety fallback for pathological repos)
    if depth >= CONFIG.depth_limit:
        if files or subdirs:
            all_entries = files + [s.name + "/" for s in subdirs]
            results.append((str(rel) + "/", all_entries))
        return results

    dir_str = str(rel) if str(rel) != "." else "."

    # Check if folder has ANY children on disk (before blacklist filtering).
    # This distinguishes truly empty folders from folders with hidden contents.
    try:
        has_any_children = any(True for c in abs_path.iterdir() if not c.is_symlink())
    except PermissionError:
        has_any_children = False

    # Recurse into subdirectories first to know which have visible content
    subdir_results: dict[str, list[tuple[str, list[str]]]] = {}
    for subdir in subdirs:
        child_rel = rel / subdir.name
        child_results = collect_tree(root, child_rel, depth + 1)
        subdir_results[subdir.name] = child_results

    # Combine files and LEAF subdirs (those with no visible content)
    # Subdirs with content will get their own lines, so don't list them here
    leaf_subdirs = [s.name + "/" for s in subdirs if not subdir_results[s.name]]
    items = files + leaf_subdirs

    if items:
        results.append((dir_str + "/", items))
    elif depth == 0:
        # Root level: show even if empty
        if has_any_children:
            results.append((dir_str + "/", []))
        else:
            results.append((dir_str + "/", ["(empty)"]))
    # For depth > 0: don't emit anything if no items - parent already shows this subdir exists

    # Add subdir results
    for subdir in subdirs:
        results.extend(subdir_results[subdir.name])

    return results


def render_index(root: Path) -> list[str]:
    """Render the file index as compact lines.

    Uses tree format for long prefixes to avoid repetition:
        packages/python_viterbo/src/viterbo/experiments/
        | algorithm_comparison/{...}
        | benchmark_hk2017/{...}
    """
    entries = collect_tree(root, Path("."), 0)

    # Group entries by tree prefix
    # Key: prefix (or "" for non-grouped), Value: list of (full_path, items)
    grouped: dict[str, list[tuple[str, list[str]]]] = defaultdict(list)

    for dir_path, items in entries:
        # Clean up the path display
        if dir_path.startswith("./"):
            clean_dir = dir_path[2:]
        else:
            clean_dir = dir_path

        # Check if this entry belongs under a tree prefix (use longest match)
        matched_prefix = ""
        for prefix in CONFIG.tree_prefixes:
            if clean_dir.startswith(prefix) and len(prefix) > len(matched_prefix):
                matched_prefix = prefix

        grouped[matched_prefix].append((clean_dir, items))

    # Render output
    lines: list[str] = []

    # First, render non-grouped entries in order they appear
    # But we need to interleave with grouped sections at the right position
    prefix_emitted: set[str] = set()

    for dir_path, items in entries:
        if dir_path.startswith("./"):
            clean_dir = dir_path[2:]
        else:
            clean_dir = dir_path

        # Find which prefix this belongs to (use longest match)
        matched_prefix = ""
        for prefix in CONFIG.tree_prefixes:
            if clean_dir.startswith(prefix) and len(prefix) > len(matched_prefix):
                matched_prefix = prefix

        if matched_prefix and matched_prefix not in prefix_emitted:
            # Emit the entire grouped section
            prefix_emitted.add(matched_prefix)
            lines.append(matched_prefix)

            # Render each tree entry
            for entry_path, entry_items in grouped[matched_prefix]:
                suffix = entry_path[len(matched_prefix):]
                if not suffix:
                    # Files directly in the prefix directory
                    compressed = compress_filenames(entry_items)
                    lines.append(f"| {compressed}")
                elif entry_items == ["(empty)"]:
                    lines.append(f"| {suffix} (empty)")
                elif not entry_items:
                    # Folder with hidden contents
                    lines.append(f"| {suffix}")
                else:
                    compressed = compress_filenames(entry_items)
                    lines.append(f"| {suffix}{compressed}")
        elif not matched_prefix:
            # Regular non-grouped entry
            if items == ["(empty)"]:
                lines.append(f"{clean_dir} (empty)")
            elif dir_path == "./":
                lines.append(compress_filenames(items))
            else:
                compressed = compress_filenames(items)
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
