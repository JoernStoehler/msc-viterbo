"""Stage 2: Generate LaTeX tables from JSON data.

Reads JSON data files from stage_build and generates LaTeX tables
for inclusion in the thesis.

Usage:
    cd packages/python_viterbo
    uv run python -m viterbo.experiments.algorithm_inventory.stage_tabulate
"""

from __future__ import annotations

import json

from viterbo.paths import get_assets_dir, get_data_dir

# =============================================================================
# Paths
# =============================================================================

DATA_DIR = get_data_dir("algorithm_inventory")
ASSETS_DIR = get_assets_dir("algorithm_inventory")


def escape_latex(s: str) -> str:
    """Escape special LaTeX characters."""
    replacements = [
        ("_", r"\_"),
        ("%", r"\%"),
        ("&", r"\&"),
        ("#", r"\#"),
        ("$", r"\$"),
    ]
    for old, new in replacements:
        s = s.replace(old, new)
    return s


def format_capacity(c: float | None) -> str:
    """Format capacity value for display."""
    if c is None:
        return "—"
    if abs(c - round(c)) < 1e-6:
        return str(int(round(c)))
    return f"{c:.4f}"


def format_time(ms: float) -> str:
    """Format time in milliseconds for display."""
    if ms == 0.0:
        return "—"
    if ms < 1000:
        return f"{ms:.0f}ms"
    return f"{ms/1000:.1f}s"


# =============================================================================
# Table generators
# =============================================================================


def generate_algorithms_table() -> str:
    """Generate LaTeX table for algorithm inventory."""
    with (DATA_DIR / "algorithms.json").open() as f:
        data = json.load(f)

    lines = [
        r"\begin{tabular}{llll}",
        r"\toprule",
        r"Algorithm & Variant & Applicability & Status \\",
        r"\midrule",
    ]

    for alg in data["algorithms"]:
        name = escape_latex(alg["name"])
        variant = escape_latex(alg["variant"]) if alg["variant"] else "—"
        applicability = escape_latex(alg["applicability"])
        status = escape_latex(alg["status"])
        lines.append(f"{name} & {variant} & {applicability} & {status} \\\\")

    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")

    return "\n".join(lines)


def generate_fixtures_table() -> str:
    """Generate LaTeX table for fixture inventory."""
    with (DATA_DIR / "fixtures.json").open() as f:
        data = json.load(f)

    lines = [
        r"\begin{tabular}{lcccc}",
        r"\toprule",
        r"Fixture & Facets & Lagrangian 2-faces & Tube-compatible & Known $c$ \\",
        r"\midrule",
    ]

    for fix in data["fixtures_4d"]:
        name = escape_latex(fix["name"])
        facets = str(fix["facets"])
        lagr = "Yes" if fix["has_lagrangian_2faces"] else "No"
        tube = "Yes" if fix["tube_compatible"] else "No"
        known_c = format_capacity(fix["known_capacity"])
        lines.append(f"{name} & {facets} & {lagr} & {tube} & {known_c} \\\\")

    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")

    return "\n".join(lines)


def generate_capacity_matrix_table() -> str:
    """Generate LaTeX table for capacity matrix."""
    with (DATA_DIR / "capacity_matrix.json").open() as f:
        data = json.load(f)

    # Group by fixture
    fixtures = {}
    for entry in data["entries"]:
        fix = entry["fixture"]
        if fix not in fixtures:
            fixtures[fix] = {}
        fixtures[fix][entry["algorithm"]] = entry

    lines = [
        r"\begin{tabular}{lcccc}",
        r"\toprule",
        r"Fixture & HK2017 naive & HK2017 graph & Tube & Time \\",
        r"\midrule",
    ]

    for fix_name, algs in fixtures.items():
        name = escape_latex(fix_name)

        naive = algs.get("hk2017_naive", {})
        graph = algs.get("hk2017_graph", {})
        tube = algs.get("tube", {})

        c_naive = format_capacity(naive.get("capacity"))
        c_graph = format_capacity(graph.get("capacity"))
        c_tube = format_capacity(tube.get("capacity"))

        # Show time for the fastest successful algorithm
        times = []
        for alg in [naive, graph, tube]:
            if alg.get("status") == "success" and alg.get("time_ms", 0) > 0:
                times.append(alg["time_ms"])
        time_str = format_time(min(times)) if times else "—"

        lines.append(f"{name} & {c_naive} & {c_graph} & {c_tube} & {time_str} \\\\")

    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")

    return "\n".join(lines)


def generate_validation_table() -> str:
    """Generate LaTeX table for validation results."""
    with (DATA_DIR / "validation_results.json").open() as f:
        data = json.load(f)

    # Group by proposition
    props = {}
    for entry in data["propositions"]:
        pid = entry["proposition_id"]
        if pid not in props:
            props[pid] = {"name": entry["proposition_name"], "results": []}
        props[pid]["results"].append(entry)

    lines = [
        r"\begin{tabular}{llll}",
        r"\toprule",
        r"Proposition & Fixture & Status & Notes \\",
        r"\midrule",
    ]

    for pid in sorted(props.keys()):
        prop = props[pid]
        first = True
        for result in prop["results"]:
            prop_col = f"{pid}: {prop['name']}" if first else ""
            first = False

            fixture = escape_latex(result["fixture"])
            status = result["status"].upper()

            # Truncate long notes
            notes = result.get("notes", "") or ""
            if len(notes) > 40:
                notes = notes[:37] + "..."
            notes = escape_latex(notes)

            lines.append(f"{prop_col} & {fixture} & {status} & {notes} \\\\")

        # Add a small gap between propositions
        if pid != sorted(props.keys())[-1]:
            lines.append(r"\addlinespace")

    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")

    return "\n".join(lines)


# =============================================================================
# Main
# =============================================================================


def main() -> None:
    """Generate all LaTeX tables."""
    ASSETS_DIR.mkdir(parents=True, exist_ok=True)

    # Generate and write tables
    tables = [
        ("table-algorithms.tex", generate_algorithms_table),
        ("table-fixtures.tex", generate_fixtures_table),
        ("table-capacity-matrix.tex", generate_capacity_matrix_table),
        ("table-validation.tex", generate_validation_table),
    ]

    for filename, generator in tables:
        content = generator()
        path = ASSETS_DIR / filename
        with path.open("w") as f:
            f.write(content)
            f.write("\n")
        print(f"Wrote {path}")

    print("\nAll tables generated successfully.")


if __name__ == "__main__":
    main()
