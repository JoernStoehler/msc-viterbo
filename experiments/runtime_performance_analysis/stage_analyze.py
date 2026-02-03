"""Stage 3: Analyze benchmarks and generate figures.

This stage:
1. Loads benchmark results from stage_build
2. Fits scaling models (time vs permutations for HK2017, time vs facets for Tube)
3. Computes R², RMSE statistics
4. Generates figures: scatter plots, residuals, speedup bars
5. Saves analysis results and figures

Usage:
    uv run python -m viterbo.experiments.runtime_performance_analysis.stage_analyze
    uv run python -m viterbo.experiments.runtime_performance_analysis.stage_analyze --config config/runtime-performance-analysis/default.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import matplotlib.pyplot as plt
import numpy as np
from scipy import stats


def load_config(path: Path) -> dict[str, Any]:
    """Load JSON config file."""
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def load_benchmarks(path: Path) -> list[dict[str, Any]]:
    """Load benchmark results from JSON."""
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


@dataclass
class ScalingModel:
    """Fitted scaling model parameters."""

    algorithm: str
    log_log_slope: float
    log_log_intercept: float
    r_squared: float
    rmse: float
    time_per_unit_us: float  # microseconds per permutation/tube
    n_samples: int


@dataclass
class AnalysisResults:
    """Complete analysis results."""

    hk2017_naive_model: ScalingModel | None
    hk2017_graph_model: ScalingModel | None
    tube_model: ScalingModel | None
    summary: dict[str, Any]


def fit_scaling_model(
    x_values: list[float], y_values: list[float], algorithm: str
) -> ScalingModel | None:
    """Fit log-log scaling model: log(y) = a + b*log(x)."""
    if len(x_values) < 2:
        return None

    # Filter out zeros
    valid = [(x, y) for x, y in zip(x_values, y_values) if x > 0 and y > 0]
    if len(valid) < 2:
        return None

    x_arr = np.array([v[0] for v in valid])
    y_arr = np.array([v[1] for v in valid])

    log_x = np.log(x_arr)
    log_y = np.log(y_arr)

    # Linear regression on log-log scale
    result = stats.linregress(log_x, log_y)
    slope = result.slope
    intercept = result.intercept
    r_squared = result.rvalue ** 2

    # Compute RMSE on original scale
    predicted_log = intercept + slope * log_x
    predicted = np.exp(predicted_log)
    rmse = float(np.sqrt(np.mean((y_arr - predicted) ** 2)))

    # Time per unit (microseconds) - use mean
    time_per_unit = float(np.mean(y_arr * 1000 / x_arr))  # y is in ms, convert to us

    return ScalingModel(
        algorithm=algorithm,
        log_log_slope=float(slope),
        log_log_intercept=float(intercept),
        r_squared=float(r_squared),
        rmse=rmse,
        time_per_unit_us=time_per_unit,
        n_samples=len(valid),
    )


def analyze_hk2017(
    benchmarks: list[dict[str, Any]], algorithm: str
) -> tuple[ScalingModel | None, list[float], list[float]]:
    """Analyze HK2017 algorithm: time vs permutations."""
    perms = []
    times = []
    for b in benchmarks:
        if not b["success"] or b["algorithm"] != algorithm:
            continue
        if b["permutations_evaluated"] > 0:
            perms.append(b["permutations_evaluated"])
            times.append(b["wall_time_ms"])

    model = fit_scaling_model(perms, times, algorithm)
    return model, perms, times


def analyze_tube(
    benchmarks: list[dict[str, Any]],
) -> tuple[ScalingModel | None, list[float], list[float]]:
    """Analyze Tube algorithm: time vs tubes explored."""
    tubes = []
    times = []
    for b in benchmarks:
        if not b["success"] or b["algorithm"] != "tube":
            continue
        if b["tubes_explored"] > 0:
            tubes.append(b["tubes_explored"])
            times.append(b["wall_time_ms"])

    model = fit_scaling_model(tubes, times, "tube")
    return model, tubes, times


def plot_scaling(
    x_values: list[float],
    y_values: list[float],
    model: ScalingModel | None,
    xlabel: str,
    ylabel: str,
    title: str,
    out_path: Path,
) -> None:
    """Create scatter plot with fitted model."""
    fig, ax = plt.subplots(figsize=(8, 6))

    ax.scatter(x_values, y_values, alpha=0.6, s=50, label="Data")

    if model is not None and len(x_values) > 0:
        x_range = np.linspace(min(x_values), max(x_values), 100)
        y_pred = np.exp(model.log_log_intercept) * x_range ** model.log_log_slope
        ax.plot(
            x_range, y_pred, "r-", linewidth=2,
            label=f"Fit: $t = {np.exp(model.log_log_intercept):.2e} \\cdot x^{{{model.log_log_slope:.2f}}}$ ($R^2={model.r_squared:.3f}$)"
        )

    ax.set_xlabel(xlabel, fontsize=12)
    ax.set_ylabel(ylabel, fontsize=12)
    ax.set_title(title, fontsize=14)
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.grid(True, alpha=0.3)
    ax.legend()

    out_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_path, dpi=150, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {out_path}")


def plot_speedup_comparison(
    benchmarks: list[dict[str, Any]], out_path: Path
) -> None:
    """Create bar chart comparing algorithm speeds."""
    # Group by algorithm
    by_algo: dict[str, list[float]] = {}
    for b in benchmarks:
        if not b["success"]:
            continue
        algo = b["algorithm"]
        by_algo.setdefault(algo, []).append(b["wall_time_ms"])

    if not by_algo:
        return

    algorithms = sorted(by_algo.keys())
    means = [np.mean(by_algo[a]) for a in algorithms]
    stds = [np.std(by_algo[a]) for a in algorithms]

    fig, ax = plt.subplots(figsize=(10, 6))

    x = np.arange(len(algorithms))
    bars = ax.bar(x, means, yerr=stds, capsize=5, alpha=0.7)

    ax.set_xlabel("Algorithm", fontsize=12)
    ax.set_ylabel("Mean Runtime (ms)", fontsize=12)
    ax.set_title("Algorithm Runtime Comparison", fontsize=14)
    ax.set_xticks(x)
    ax.set_xticklabels([a.replace("_", " ") for a in algorithms])
    ax.grid(True, alpha=0.3, axis="y")

    # Add value labels on bars
    for bar, mean in zip(bars, means):
        ax.annotate(
            f"{mean:.2f}",
            xy=(bar.get_x() + bar.get_width() / 2, bar.get_height()),
            ha="center", va="bottom", fontsize=10
        )

    out_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_path, dpi=150, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {out_path}")


def plot_time_by_facets(
    benchmarks: list[dict[str, Any]], out_path: Path
) -> None:
    """Create line plot of runtime vs facet count per algorithm."""
    # Group by (algorithm, n_facets)
    grouped: dict[str, dict[int, list[float]]] = {}
    for b in benchmarks:
        if not b["success"]:
            continue
        algo = b["algorithm"]
        n_facets = b["n_facets"]
        grouped.setdefault(algo, {}).setdefault(n_facets, []).append(b["wall_time_ms"])

    if not grouped:
        return

    fig, ax = plt.subplots(figsize=(10, 6))

    markers = {"hk2017_naive": "o", "hk2017_graph": "s", "tube": "^"}
    colors = {"hk2017_naive": "blue", "hk2017_graph": "green", "tube": "red"}

    for algo in sorted(grouped.keys()):
        facet_data = grouped[algo]
        facets = sorted(facet_data.keys())
        means = [np.mean(facet_data[f]) for f in facets]
        stds = [np.std(facet_data[f]) for f in facets]

        ax.errorbar(
            facets, means, yerr=stds,
            marker=markers.get(algo, "o"),
            color=colors.get(algo, "gray"),
            label=algo.replace("_", " "),
            capsize=3, linewidth=2, markersize=8
        )

    ax.set_xlabel("Number of Facets", fontsize=12)
    ax.set_ylabel("Runtime (ms)", fontsize=12)
    ax.set_title("Runtime vs Facet Count", fontsize=14)
    ax.set_yscale("log")
    ax.grid(True, alpha=0.3)
    ax.legend()

    out_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_path, dpi=150, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {out_path}")


def run_analysis(benchmarks: list[dict[str, Any]]) -> AnalysisResults:
    """Run the full analysis pipeline."""
    # Analyze HK2017 naive
    hk2017_naive_model, _, _ = analyze_hk2017(benchmarks, "hk2017_naive")

    # Analyze HK2017 graph
    hk2017_graph_model, _, _ = analyze_hk2017(benchmarks, "hk2017_graph")

    # Analyze Tube
    tube_model, _, _ = analyze_tube(benchmarks)

    # Build summary
    summary = {
        "total_benchmarks": len(benchmarks),
        "successful_benchmarks": sum(1 for b in benchmarks if b["success"]),
        "algorithms_tested": list(set(b["algorithm"] for b in benchmarks)),
    }

    if hk2017_naive_model:
        summary["hk2017_naive_formula"] = (
            f"t_ms = {math.exp(hk2017_naive_model.log_log_intercept):.2e} * perms^{hk2017_naive_model.log_log_slope:.2f}"
        )
        summary["hk2017_naive_r_squared"] = hk2017_naive_model.r_squared
        summary["hk2017_naive_time_per_perm_us"] = hk2017_naive_model.time_per_unit_us

    if hk2017_graph_model:
        summary["hk2017_graph_formula"] = (
            f"t_ms = {math.exp(hk2017_graph_model.log_log_intercept):.2e} * perms^{hk2017_graph_model.log_log_slope:.2f}"
        )
        summary["hk2017_graph_r_squared"] = hk2017_graph_model.r_squared
        summary["hk2017_graph_time_per_perm_us"] = hk2017_graph_model.time_per_unit_us

    if tube_model:
        summary["tube_formula"] = (
            f"t_ms = {math.exp(tube_model.log_log_intercept):.2e} * tubes^{tube_model.log_log_slope:.2f}"
        )
        summary["tube_r_squared"] = tube_model.r_squared
        summary["tube_time_per_tube_us"] = tube_model.time_per_unit_us

    return AnalysisResults(
        hk2017_naive_model=hk2017_naive_model,
        hk2017_graph_model=hk2017_graph_model,
        tube_model=tube_model,
        summary=summary,
    )


def main(config_path: str = "config/runtime-performance-analysis/default.json") -> None:
    """Run analysis and generate figures."""
    cfg = load_config(Path(config_path))
    data_dir = Path(cfg["output_dir"])
    assets_dir = Path(cfg["assets_dir"])

    # Load benchmark results
    benchmarks_path = data_dir / "benchmark_results.json"
    if not benchmarks_path.exists():
        raise FileNotFoundError(
            f"{benchmarks_path} not found. Run stage_build first."
        )

    benchmarks = load_benchmarks(benchmarks_path)
    print(f"Loaded {len(benchmarks)} benchmark results")

    # Run analysis
    results = run_analysis(benchmarks)

    # Save analysis results
    analysis_path = data_dir / "analysis_results.json"
    analysis_data = {
        "hk2017_naive_model": asdict(results.hk2017_naive_model) if results.hk2017_naive_model else None,
        "hk2017_graph_model": asdict(results.hk2017_graph_model) if results.hk2017_graph_model else None,
        "tube_model": asdict(results.tube_model) if results.tube_model else None,
        "summary": results.summary,
    }
    with analysis_path.open("w", encoding="utf-8") as f:
        json.dump(analysis_data, f, indent=2)
    print(f"Wrote analysis results to {analysis_path}")

    # Generate figures
    assets_dir.mkdir(parents=True, exist_ok=True)

    # HK2017 naive scaling plot
    hk2017_naive_model, naive_perms, naive_times = analyze_hk2017(benchmarks, "hk2017_naive")
    if naive_perms:
        plot_scaling(
            naive_perms, naive_times, hk2017_naive_model,
            "Permutations Evaluated", "Runtime (ms)",
            "HK2017 Naive: Runtime vs Permutations",
            assets_dir / "hk2017-naive-scaling.png"
        )

    # HK2017 graph scaling plot
    hk2017_graph_model, graph_perms, graph_times = analyze_hk2017(benchmarks, "hk2017_graph")
    if graph_perms:
        plot_scaling(
            graph_perms, graph_times, hk2017_graph_model,
            "Permutations Evaluated", "Runtime (ms)",
            "HK2017 Graph: Runtime vs Permutations",
            assets_dir / "hk2017-graph-scaling.png"
        )

    # Tube scaling plot
    tube_model, tube_explored, tube_times = analyze_tube(benchmarks)
    if tube_explored:
        plot_scaling(
            tube_explored, tube_times, tube_model,
            "Tubes Explored", "Runtime (ms)",
            "Tube: Runtime vs Tubes Explored",
            assets_dir / "tube-scaling.png"
        )

    # Algorithm comparison bar chart
    plot_speedup_comparison(benchmarks, assets_dir / "algorithm-comparison.png")

    # Time by facets line plot
    plot_time_by_facets(benchmarks, assets_dir / "time-by-facets.png")

    # Print summary
    print("\n" + "=" * 60)
    print("ANALYSIS SUMMARY")
    print("=" * 60)
    for key, value in results.summary.items():
        print(f"  {key}: {value}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Analyze benchmark results")
    parser.add_argument(
        "--config",
        default="config/runtime-performance-analysis/default.json",
        help="Path to config file",
    )
    args = parser.parse_args()
    main(args.config)
