"""Stage 2: Generate LaTeX tables from benchmark results.

This stage:
1. Loads benchmark results from stage_build
2. Generates LaTeX tables:
   - Runtime by facet count
   - Algorithm comparison
   - Prediction formulas
3. Saves tables to thesis assets directory

Usage:
    uv run python -m viterbo.experiments.runtime_performance_analysis.stage_tabulate
    uv run python -m viterbo.experiments.runtime_performance_analysis.stage_tabulate --config config/runtime-performance-analysis/default.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np


def load_config(path: Path) -> dict[str, Any]:
    """Load JSON config file."""
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def load_benchmarks(path: Path) -> list[dict[str, Any]]:
    """Load benchmark results from JSON."""
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def compute_stats(values: list[float]) -> dict[str, float]:
    """Compute mean, std, min, max for a list of values."""
    if not values:
        return {"mean": 0, "std": 0, "min": 0, "max": 0}
    return {
        "mean": float(np.mean(values)),
        "std": float(np.std(values)),
        "min": float(np.min(values)),
        "max": float(np.max(values)),
    }


def generate_runtime_by_facets_table(benchmarks: list[dict[str, Any]]) -> str:
    """Generate LaTeX table: runtime by facet count for each algorithm."""
    # Group by (algorithm, n_facets)
    grouped: dict[tuple[str, int], list[float]] = {}
    for b in benchmarks:
        if not b["success"]:
            continue
        key = (b["algorithm"], b["n_facets"])
        grouped.setdefault(key, []).append(b["wall_time_ms"])

    # Get all algorithms and facet counts
    algorithms = sorted(set(k[0] for k in grouped.keys()))
    facet_counts = sorted(set(k[1] for k in grouped.keys()))

    # Build table
    lines = [
        r"\begin{table}[htbp]",
        r"\centering",
        r"\caption{Mean runtime (ms) by facet count and algorithm}",
        r"\label{tab:runtime-by-facets}",
        r"\begin{tabular}{r" + "r" * len(algorithms) + "}",
        r"\toprule",
        r"Facets & " + " & ".join(algo.replace("_", r"\_") for algo in algorithms) + r" \\",
        r"\midrule",
    ]

    for n_facets in facet_counts:
        row = [str(n_facets)]
        for algo in algorithms:
            key = (algo, n_facets)
            if key in grouped:
                stats = compute_stats(grouped[key])
                row.append(f"{stats['mean']:.2f}")
            else:
                row.append("---")
        lines.append(" & ".join(row) + r" \\")

    lines.extend([
        r"\bottomrule",
        r"\end{tabular}",
        r"\end{table}",
    ])

    return "\n".join(lines)


def generate_algorithm_comparison_table(benchmarks: list[dict[str, Any]]) -> str:
    """Generate LaTeX table: algorithm comparison on common polytopes."""
    # Find polytopes where all three algorithms succeeded
    by_polytope: dict[str, dict[str, list[float]]] = {}
    for b in benchmarks:
        if not b["success"]:
            continue
        pid = b["polytope_id"]
        algo = b["algorithm"]
        by_polytope.setdefault(pid, {}).setdefault(algo, []).append(b["wall_time_ms"])

    # Find polytopes with all three algorithms
    all_algos = {"hk2017_naive", "hk2017_graph", "tube"}
    common_polytopes = [
        pid for pid, algos in by_polytope.items()
        if all_algos.issubset(algos.keys())
    ]

    lines = [
        r"\begin{table}[htbp]",
        r"\centering",
        r"\caption{Algorithm comparison on polytopes suitable for all algorithms}",
        r"\label{tab:algorithm-comparison}",
        r"\begin{tabular}{lrrrr}",
        r"\toprule",
        r"Polytope & HK2017 naive & HK2017 graph & Tube & Speedup \\",
        r"\midrule",
    ]

    for pid in sorted(common_polytopes)[:10]:  # Limit to 10 for readability
        algos = by_polytope[pid]
        naive_mean = np.mean(algos["hk2017_naive"])
        graph_mean = np.mean(algos["hk2017_graph"])
        tube_mean = np.mean(algos["tube"])
        speedup = naive_mean / tube_mean if tube_mean > 0 else 0

        pid_escaped = pid.replace("_", r"\_")
        lines.append(
            f"{pid_escaped} & {naive_mean:.2f} & {graph_mean:.2f} & {tube_mean:.2f} & {speedup:.1f}x" + r" \\"
        )

    lines.extend([
        r"\bottomrule",
        r"\end{tabular}",
        r"\end{table}",
    ])

    return "\n".join(lines)


def generate_prediction_formulas_table(benchmarks: list[dict[str, Any]]) -> str:
    """Generate LaTeX table: empirical prediction formulas."""
    # Compute average time per permutation for HK2017
    hk2017_times: list[float] = []
    hk2017_perms: list[int] = []
    for b in benchmarks:
        if not b["success"]:
            continue
        if b["algorithm"] in ("hk2017_naive", "hk2017_graph"):
            if b["permutations_evaluated"] > 0:
                hk2017_times.append(b["wall_time_ms"])
                hk2017_perms.append(b["permutations_evaluated"])

    # Time per permutation in microseconds
    if hk2017_times and hk2017_perms:
        time_per_perm_us = [
            (t * 1000) / p for t, p in zip(hk2017_times, hk2017_perms) if p > 0
        ]
        avg_time_per_perm = np.mean(time_per_perm_us) if time_per_perm_us else 0
    else:
        avg_time_per_perm = 0

    # Compute average time per tube for Tube algorithm
    tube_times: list[float] = []
    tube_explored: list[int] = []
    for b in benchmarks:
        if not b["success"]:
            continue
        if b["algorithm"] == "tube":
            if b["tubes_explored"] > 0:
                tube_times.append(b["wall_time_ms"])
                tube_explored.append(b["tubes_explored"])

    if tube_times and tube_explored:
        time_per_tube_us = [
            (t * 1000) / e for t, e in zip(tube_times, tube_explored) if e > 0
        ]
        avg_time_per_tube = np.mean(time_per_tube_us) if time_per_tube_us else 0
    else:
        avg_time_per_tube = 0

    lines = [
        r"\begin{table}[htbp]",
        r"\centering",
        r"\caption{Empirical runtime prediction formulas}",
        r"\label{tab:prediction-formulas}",
        r"\begin{tabular}{llr}",
        r"\toprule",
        r"Algorithm & Formula & Constant \\",
        r"\midrule",
        f"HK2017 (naive/graph) & $t = \\alpha \\cdot P$ & $\\alpha = {avg_time_per_perm:.2f}$ $\\mu$s/perm" + r" \\",
        f"Tube & $t = \\beta \\cdot T$ & $\\beta = {avg_time_per_tube:.2f}$ $\\mu$s/tube" + r" \\",
        r"\bottomrule",
        r"\end{tabular}",
        r"\end{table}",
    ]

    return "\n".join(lines)


def main(config_path: str = "config/runtime-performance-analysis/default.json") -> None:
    """Generate LaTeX tables from benchmark results."""
    cfg = load_config(Path(config_path))
    data_dir = Path(cfg["output_dir"])
    assets_dir = Path(cfg["assets_dir"])

    # Ensure assets directory exists
    assets_dir.mkdir(parents=True, exist_ok=True)

    # Load benchmark results
    benchmarks_path = data_dir / "benchmark_results.json"
    if not benchmarks_path.exists():
        raise FileNotFoundError(
            f"{benchmarks_path} not found. Run stage_build first."
        )

    benchmarks = load_benchmarks(benchmarks_path)
    print(f"Loaded {len(benchmarks)} benchmark results")

    # Generate tables
    tables = {
        "runtime-by-facets.tex": generate_runtime_by_facets_table(benchmarks),
        "algorithm-comparison.tex": generate_algorithm_comparison_table(benchmarks),
        "prediction-formulas.tex": generate_prediction_formulas_table(benchmarks),
    }

    for filename, content in tables.items():
        out_path = assets_dir / filename
        with out_path.open("w", encoding="utf-8") as f:
            f.write(content)
        print(f"Wrote {out_path}")

    print(f"\nGenerated {len(tables)} LaTeX tables")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate LaTeX tables from benchmarks")
    parser.add_argument(
        "--config",
        default="config/runtime-performance-analysis/default.json",
        help="Path to config file",
    )
    args = parser.parse_args()
    main(args.config)
