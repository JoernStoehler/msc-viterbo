"""Stage 2: Analyze HK2017 timing data and build scaling models.

This stage:
1. Loads timing data from stage_build
2. Computes statistics per facet count
3. Fits scaling models (factorial, exponential)
4. Builds prediction formulas
5. Computes budget inversion (what can run in X seconds)

Usage:
    uv run python -m viterbo.experiments.benchmark_hk2017.stage_analyze
    uv run python -m viterbo.experiments.benchmark_hk2017.stage_analyze --config config/benchmark-hk2017/quick.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any

import numpy as np
from scipy import stats


def load_config(path: Path) -> dict[str, Any]:
    """Load JSON config file."""
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def load_timings(path: Path) -> list[dict[str, Any]]:
    """Load timing results from JSON."""
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def theoretical_permutation_count(n_facets: int) -> int:
    """Compute theoretical number of permutations for naive HK2017.

    Total = Σ_{k=2}^F C(F,k) × k! = Σ_{k=2}^F F!/(F-k)!
    """
    total = 0
    for k in range(2, n_facets + 1):
        # F! / (F-k)! = P(F, k) = F × (F-1) × ... × (F-k+1)
        perm = 1
        for i in range(n_facets - k + 1, n_facets + 1):
            perm *= i
        total += perm
    return total


@dataclass
class FacetStats:
    """Statistics for a single facet count."""

    n_facets: int
    n_samples: int
    theoretical_perms: int
    observed_perms_mean: float
    observed_perms_std: float
    wall_time_mean_ms: float
    wall_time_std_ms: float
    time_per_perm_us: float  # microseconds per permutation
    capacity_mean: float
    capacity_std: float


@dataclass
class ScalingModel:
    """Fitted scaling model parameters."""

    # log(time) = a + b * log(perms) model
    log_log_slope: float
    log_log_intercept: float
    log_log_r_squared: float

    # Direct fit: time = c * perms^d
    power_coefficient: float
    power_exponent: float

    # Time per permutation (microseconds)
    time_per_perm_us_mean: float
    time_per_perm_us_std: float


@dataclass
class BudgetTable:
    """Budget inversion: what can run in X seconds."""

    budget_seconds: float
    max_facets_estimated: int
    max_perms_estimated: int
    note: str


@dataclass
class AnalysisResult:
    """Complete analysis results."""

    facet_stats: list[FacetStats]
    scaling_model: ScalingModel
    budget_tables: list[BudgetTable]
    summary: dict[str, Any]


def compute_facet_stats(timings: list[dict[str, Any]]) -> list[FacetStats]:
    """Compute statistics grouped by facet count."""
    # Group by n_facets
    by_facets: dict[int, list[dict[str, Any]]] = {}
    for t in timings:
        if not t["success"]:
            continue
        f = t["n_facets"]
        by_facets.setdefault(f, []).append(t)

    results = []
    for n_facets in sorted(by_facets.keys()):
        samples = by_facets[n_facets]
        n = len(samples)

        times = [s["wall_time_ms"] for s in samples]
        perms = [s["permutations_evaluated"] for s in samples]
        caps = [s["capacity"] for s in samples]

        theoretical = theoretical_permutation_count(n_facets)

        # Time per permutation (convert ms to us)
        time_per_perm = [
            (t * 1000) / p if p > 0 else 0 for t, p in zip(times, perms)
        ]

        results.append(
            FacetStats(
                n_facets=n_facets,
                n_samples=n,
                theoretical_perms=theoretical,
                observed_perms_mean=float(np.mean(perms)),
                observed_perms_std=float(np.std(perms)) if n > 1 else 0,
                wall_time_mean_ms=float(np.mean(times)),
                wall_time_std_ms=float(np.std(times)) if n > 1 else 0,
                time_per_perm_us=float(np.mean(time_per_perm)),
                capacity_mean=float(np.mean(caps)),
                capacity_std=float(np.std(caps)) if n > 1 else 0,
            )
        )

    return results


def fit_scaling_model(facet_stats: list[FacetStats]) -> ScalingModel:
    """Fit scaling models to the timing data."""
    # Need at least 2 points
    if len(facet_stats) < 2:
        return ScalingModel(
            log_log_slope=1.0,
            log_log_intercept=0.0,
            log_log_r_squared=0.0,
            power_coefficient=1.0,
            power_exponent=1.0,
            time_per_perm_us_mean=0.0,
            time_per_perm_us_std=0.0,
        )

    # Collect data points
    log_perms = []
    log_times = []
    time_per_perms = []

    for s in facet_stats:
        if s.observed_perms_mean > 0 and s.wall_time_mean_ms > 0:
            log_perms.append(math.log(s.observed_perms_mean))
            log_times.append(math.log(s.wall_time_mean_ms))
            time_per_perms.append(s.time_per_perm_us)

    if len(log_perms) < 2:
        return ScalingModel(
            log_log_slope=1.0,
            log_log_intercept=0.0,
            log_log_r_squared=0.0,
            power_coefficient=1.0,
            power_exponent=1.0,
            time_per_perm_us_mean=float(np.mean(time_per_perms)) if time_per_perms else 0,
            time_per_perm_us_std=float(np.std(time_per_perms)) if len(time_per_perms) > 1 else 0,
        )

    # Linear regression on log-log scale
    slope, intercept, r_value, _, _ = stats.linregress(log_perms, log_times)

    # Convert to power law: time_ms = exp(intercept) * perms^slope
    power_coef = math.exp(intercept)
    power_exp = slope

    return ScalingModel(
        log_log_slope=slope,
        log_log_intercept=intercept,
        log_log_r_squared=r_value**2,
        power_coefficient=power_coef,
        power_exponent=power_exp,
        time_per_perm_us_mean=float(np.mean(time_per_perms)),
        time_per_perm_us_std=float(np.std(time_per_perms)) if len(time_per_perms) > 1 else 0,
    )


def compute_budget_tables(
    scaling_model: ScalingModel, facet_stats: list[FacetStats]
) -> list[BudgetTable]:
    """Compute budget inversion tables for common time budgets."""
    budgets = [1.0, 5.0, 10.0, 30.0, 60.0, 300.0]  # seconds
    results = []

    # Use time_per_perm to estimate: time = perms * time_per_perm_us / 1e6 seconds
    time_per_perm_s = scaling_model.time_per_perm_us_mean / 1e6

    if time_per_perm_s <= 0:
        return results

    for budget in budgets:
        # max_perms = budget / time_per_perm_s
        max_perms = int(budget / time_per_perm_s)

        # Find max facets where theoretical_perms <= max_perms
        max_facets = 2
        for f in range(2, 20):
            if theoretical_permutation_count(f) <= max_perms:
                max_facets = f
            else:
                break

        note = ""
        if max_facets > 10:
            note = "FFI limit is 10 facets"
            max_facets = 10

        results.append(
            BudgetTable(
                budget_seconds=budget,
                max_facets_estimated=max_facets,
                max_perms_estimated=theoretical_permutation_count(max_facets),
                note=note,
            )
        )

    return results


def run_analysis(data_dir: Path) -> AnalysisResult:
    """Run the full analysis pipeline."""
    timings_path = data_dir / "timings.json"
    timings = load_timings(timings_path)

    print(f"Loaded {len(timings)} timing records")

    # Compute stats
    facet_stats = compute_facet_stats(timings)
    print(f"Computed stats for {len(facet_stats)} facet counts")

    # Fit scaling model
    scaling_model = fit_scaling_model(facet_stats)
    print(f"Fitted scaling model: time_ms = {scaling_model.power_coefficient:.4e} * perms^{scaling_model.power_exponent:.3f}")
    print(f"R² = {scaling_model.log_log_r_squared:.4f}")

    # Compute budget tables
    budget_tables = compute_budget_tables(scaling_model, facet_stats)

    # Build summary
    summary = {
        "total_records": len(timings),
        "successful_records": sum(1 for t in timings if t["success"]),
        "facet_counts_tested": [s.n_facets for s in facet_stats],
        "scaling_formula": f"time_ms = {scaling_model.power_coefficient:.4e} * perms^{scaling_model.power_exponent:.3f}",
        "time_per_perm_us": scaling_model.time_per_perm_us_mean,
        "r_squared": scaling_model.log_log_r_squared,
        "practical_limit": "10 facets (FFI enforced)",
    }

    return AnalysisResult(
        facet_stats=facet_stats,
        scaling_model=scaling_model,
        budget_tables=budget_tables,
        summary=summary,
    )


def main(config_path: str = "config/benchmark-hk2017/default.json") -> None:
    """Run analysis and save results."""
    cfg = load_config(Path(config_path))
    data_dir = Path(cfg["output_dir"])

    print(f"Analyzing HK2017 benchmark data from: {data_dir}")

    result = run_analysis(data_dir)

    # Save analysis
    out_path = data_dir / "analysis.json"
    with out_path.open("w", encoding="utf-8") as f:
        json.dump(
            {
                "facet_stats": [asdict(s) for s in result.facet_stats],
                "scaling_model": asdict(result.scaling_model),
                "budget_tables": [asdict(b) for b in result.budget_tables],
                "summary": result.summary,
            },
            f,
            indent=2,
        )

    print(f"\nWrote analysis to {out_path}")

    # Print summary
    print("\n" + "=" * 60)
    print("ANALYSIS SUMMARY")
    print("=" * 60)

    print("\nStatistics by facet count:")
    print(f"{'Facets':>7} {'Perms (theory)':>15} {'Perms (obs)':>12} {'Time (ms)':>12} {'us/perm':>10}")
    print("-" * 60)
    for s in result.facet_stats:
        print(
            f"{s.n_facets:>7} {s.theoretical_perms:>15,} {s.observed_perms_mean:>12,.0f} "
            f"{s.wall_time_mean_ms:>12.2f} {s.time_per_perm_us:>10.2f}"
        )

    print(f"\nScaling model: {result.summary['scaling_formula']}")
    print(f"R² = {result.scaling_model.log_log_r_squared:.4f}")
    print(f"Mean time per permutation: {result.scaling_model.time_per_perm_us_mean:.2f} µs")

    print("\nBudget table (what can you compute in X seconds):")
    print(f"{'Budget':>10} {'Max Facets':>12} {'Max Perms':>15} {'Note'}")
    print("-" * 60)
    for b in result.budget_tables:
        print(f"{b.budget_seconds:>10.0f}s {b.max_facets_estimated:>12} {b.max_perms_estimated:>15,} {b.note}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Analyze HK2017 benchmark data")
    parser.add_argument(
        "--config",
        default="config/benchmark-hk2017/default.json",
        help="Path to config file",
    )
    args = parser.parse_args()
    main(args.config)
