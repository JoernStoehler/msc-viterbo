"""Stage 3: Plot HK2017 benchmark results.

This stage creates visualizations:
1. Runtime vs facet count (log scale)
2. Observed vs theoretical permutation count
3. Time per permutation distribution
4. Prediction model fit quality

Usage:
    uv run python -m viterbo.experiments.benchmark_hk2017.stage_plot
    uv run python -m viterbo.experiments.benchmark_hk2017.stage_plot --config config/benchmark-hk2017/quick.json
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import matplotlib.pyplot as plt
import numpy as np


def load_config(path: Path) -> dict[str, Any]:
    """Load JSON config file."""
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def load_analysis(path: Path) -> dict[str, Any]:
    """Load analysis results from JSON."""
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def load_timings(path: Path) -> list[dict[str, Any]]:
    """Load timing results from JSON."""
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def theoretical_permutation_count(n_facets: int) -> int:
    """Compute theoretical number of permutations for naive HK2017."""
    total = 0
    for k in range(2, n_facets + 1):
        perm = 1
        for i in range(n_facets - k + 1, n_facets + 1):
            perm *= i
        total += perm
    return total


def plot_runtime_vs_facets(
    timings: list[dict[str, Any]], analysis: dict[str, Any], output_path: Path
) -> None:
    """Plot runtime vs facet count with model fit."""
    fig, ax = plt.subplots(figsize=(10, 6))

    # Scatter plot of individual runs
    successful = [t for t in timings if t["success"]]
    facets = [t["n_facets"] for t in successful]
    times = [t["wall_time_ms"] for t in successful]

    ax.scatter(facets, times, alpha=0.5, label="Individual runs", s=30)

    # Plot mean per facet count
    stats = analysis["facet_stats"]
    mean_facets = [s["n_facets"] for s in stats]
    mean_times = [s["wall_time_mean_ms"] for s in stats]
    std_times = [s["wall_time_std_ms"] for s in stats]

    ax.errorbar(
        mean_facets,
        mean_times,
        yerr=std_times,
        fmt="o-",
        color="red",
        markersize=8,
        label="Mean ± std",
        capsize=3,
    )

    # Plot model prediction
    model = analysis["scaling_model"]
    if model["time_per_perm_us_mean"] > 0:
        pred_facets = np.arange(min(mean_facets), max(mean_facets) + 1)
        pred_perms = [theoretical_permutation_count(int(f)) for f in pred_facets]
        pred_times = [
            p * model["time_per_perm_us_mean"] / 1000
            for p in pred_perms  # ms
        ]
        ax.plot(
            pred_facets,
            pred_times,
            "--",
            color="green",
            linewidth=2,
            label=f"Model (R²={model['log_log_r_squared']:.3f})",
        )

    ax.set_xlabel("Number of Facets")
    ax.set_ylabel("Wall Time (ms)")
    ax.set_title("HK2017 Runtime vs Facet Count")
    ax.set_yscale("log")
    ax.legend()
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150)
    plt.close()
    print(f"Saved: {output_path}")


def plot_perms_observed_vs_theory(analysis: dict[str, Any], output_path: Path) -> None:
    """Plot observed vs theoretical permutation count."""
    fig, ax = plt.subplots(figsize=(8, 6))

    stats = analysis["facet_stats"]
    facets = [s["n_facets"] for s in stats]
    observed = [s["observed_perms_mean"] for s in stats]
    theoretical = [s["theoretical_perms"] for s in stats]

    x = np.arange(len(facets))
    width = 0.35

    ax.bar(x - width / 2, theoretical, width, label="Theoretical", alpha=0.8)
    ax.bar(x + width / 2, observed, width, label="Observed (mean)", alpha=0.8)

    ax.set_xlabel("Number of Facets")
    ax.set_ylabel("Permutation Count")
    ax.set_title("Theoretical vs Observed Permutations")
    ax.set_xticks(x)
    ax.set_xticklabels(facets)
    ax.set_yscale("log")
    ax.legend()
    ax.grid(True, alpha=0.3, axis="y")

    plt.tight_layout()
    plt.savefig(output_path, dpi=150)
    plt.close()
    print(f"Saved: {output_path}")


def plot_time_per_perm(
    timings: list[dict[str, Any]], analysis: dict[str, Any], output_path: Path
) -> None:
    """Plot time per permutation distribution."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))

    # Compute time per perm for each run
    successful = [
        t for t in timings if t["success"] and t["permutations_evaluated"] > 0
    ]
    time_per_perm = [
        (t["wall_time_ms"] * 1000) / t["permutations_evaluated"]  # microseconds
        for t in successful
    ]
    facets = [t["n_facets"] for t in successful]

    # Histogram
    ax1.hist(time_per_perm, bins=20, edgecolor="black", alpha=0.7)
    ax1.axvline(
        analysis["scaling_model"]["time_per_perm_us_mean"],
        color="red",
        linestyle="--",
        label=f"Mean: {analysis['scaling_model']['time_per_perm_us_mean']:.2f} µs",
    )
    ax1.set_xlabel("Time per Permutation (µs)")
    ax1.set_ylabel("Count")
    ax1.set_title("Distribution of Time per Permutation")
    ax1.legend()

    # By facet count
    ax2.scatter(facets, time_per_perm, alpha=0.5)
    ax2.axhline(
        analysis["scaling_model"]["time_per_perm_us_mean"],
        color="red",
        linestyle="--",
        label="Mean",
    )
    ax2.set_xlabel("Number of Facets")
    ax2.set_ylabel("Time per Permutation (µs)")
    ax2.set_title("Time per Permutation vs Facet Count")
    ax2.legend()

    plt.tight_layout()
    plt.savefig(output_path, dpi=150)
    plt.close()
    print(f"Saved: {output_path}")


def plot_budget_table(analysis: dict[str, Any], output_path: Path) -> None:
    """Plot budget table as a visual guide."""
    fig, ax = plt.subplots(figsize=(10, 6))

    budget_tables = analysis["budget_tables"]
    budgets = [b["budget_seconds"] for b in budget_tables]
    max_facets = [b["max_facets_estimated"] for b in budget_tables]

    ax.bar(range(len(budgets)), max_facets, tick_label=[f"{b}s" for b in budgets])

    # Add horizontal line at FFI limit
    ax.axhline(10, color="red", linestyle="--", label="FFI limit (10 facets)")

    ax.set_xlabel("Time Budget")
    ax.set_ylabel("Maximum Facets")
    ax.set_title("What Can You Compute? (Budget → Max Facets)")
    ax.legend()

    # Add value labels on bars
    for i, (budget, facets) in enumerate(zip(budgets, max_facets)):
        ax.text(i, facets + 0.1, str(facets), ha="center", va="bottom")

    plt.tight_layout()
    plt.savefig(output_path, dpi=150)
    plt.close()
    print(f"Saved: {output_path}")


def main(config_path: str = "config/benchmark-hk2017/default.json") -> None:
    """Generate all plots."""
    cfg = load_config(Path(config_path))
    data_dir = Path(cfg["output_dir"])

    print(f"Generating plots from: {data_dir}")

    # Load data
    timings = load_timings(data_dir / "timings.json")
    analysis = load_analysis(data_dir / "analysis.json")

    # Create output directory for plots
    plots_dir = data_dir / "plots"
    plots_dir.mkdir(exist_ok=True)

    # Generate plots
    plot_runtime_vs_facets(timings, analysis, plots_dir / "runtime_vs_facets.png")
    plot_perms_observed_vs_theory(analysis, plots_dir / "perms_observed_vs_theory.png")
    plot_time_per_perm(timings, analysis, plots_dir / "time_per_perm.png")
    plot_budget_table(analysis, plots_dir / "budget_table.png")

    print(f"\nAll plots saved to {plots_dir}/")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Plot HK2017 benchmark results")
    parser.add_argument(
        "--config",
        default="config/benchmark-hk2017/default.json",
        help="Path to config file",
    )
    args = parser.parse_args()
    main(args.config)
