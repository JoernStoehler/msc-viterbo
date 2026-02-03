"""Stage 1: Generate benchmarks for runtime performance analysis.

This stage:
1. Constructs fixed fixture polytopes in Python
2. Generates random polytopes (Python for HK2017, FFI for Tube)
3. Times each (polytope, algorithm) pair
4. Saves benchmark data to JSON

Usage:
    uv run python -m viterbo.experiments.runtime_performance_analysis.stage_build
    uv run python -m viterbo.experiments.runtime_performance_analysis.stage_build --config config/runtime-performance-analysis/default.json
"""

from __future__ import annotations

import argparse
import json
import math
import random
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import numpy as np
from scipy.spatial import ConvexHull

try:
    import rust_viterbo_ffi as ffi
except ImportError:
    ffi = None


@dataclass
class BenchmarkResult:
    """Result of benchmarking a single polytope with one algorithm."""

    polytope_id: str
    polytope_family: str
    n_facets: int
    algorithm: str
    rep: int
    wall_time_ms: float
    capacity: float
    permutations_evaluated: int
    permutations_rejected: int
    tubes_explored: int
    tubes_pruned: int
    success: bool
    error: str | None = None


# =============================================================================
# Fixture Construction (Python-side)
# =============================================================================


def make_tesseract_hrep() -> tuple[list[list[float]], list[float]]:
    """Create tesseract [-1, 1]^4 in H-representation."""
    normals = [
        [1.0, 0.0, 0.0, 0.0],
        [-1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, -1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, -1.0, 0.0],
        [0.0, 0.0, 0.0, 1.0],
        [0.0, 0.0, 0.0, -1.0],
    ]
    heights = [1.0] * 8
    return normals, heights


def make_cross_polytope_hrep() -> tuple[list[list[float]], list[float]]:
    """Create unit cross-polytope (16-cell) in H-representation."""
    normals = []
    for s1 in [-1.0, 1.0]:
        for s2 in [-1.0, 1.0]:
            for s3 in [-1.0, 1.0]:
                for s4 in [-1.0, 1.0]:
                    normals.append([s1 / 2.0, s2 / 2.0, s3 / 2.0, s4 / 2.0])
    heights = [0.5] * 16
    return normals, heights


def make_24_cell_hrep() -> tuple[list[list[float]], list[float]]:
    """Create unit 24-cell in H-representation."""
    s = 1.0 / math.sqrt(2.0)
    normals = []
    pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    for i, j in pairs:
        for s1 in [-1.0, 1.0]:
            for s2 in [-1.0, 1.0]:
                n = [0.0, 0.0, 0.0, 0.0]
                n[i] = s1 * s
                n[j] = s2 * s
                normals.append(n)
    heights = [s] * 24
    return normals, heights


def make_simplex_hrep() -> tuple[list[list[float]], list[float]]:
    """Create 4-simplex (5-cell) in H-representation."""
    sqrt19 = math.sqrt(19.0)
    n4 = [1.0 / 2.0, 1.0 / 2.0, 1.0 / 2.0, 1.0 / 2.0]
    h4 = 0.5
    n0 = [-4.0 / sqrt19, 1.0 / sqrt19, 1.0 / sqrt19, 1.0 / sqrt19]
    h0 = 1.0 / sqrt19
    n1 = [1.0 / sqrt19, -4.0 / sqrt19, 1.0 / sqrt19, 1.0 / sqrt19]
    h1 = 1.0 / sqrt19
    n2 = [1.0 / sqrt19, 1.0 / sqrt19, -4.0 / sqrt19, 1.0 / sqrt19]
    h2 = 1.0 / sqrt19
    n3 = [1.0 / sqrt19, 1.0 / sqrt19, 1.0 / sqrt19, -4.0 / sqrt19]
    h3 = 1.0 / sqrt19
    return [n0, n1, n2, n3, n4], [h0, h1, h2, h3, h4]


# =============================================================================
# Random Polytope Generation (Python-side, for HK2017)
# =============================================================================


def vertices_to_hrep(
    vertices: np.ndarray,
) -> tuple[list[list[float]], list[float]]:
    """Convert V-representation to H-representation using scipy ConvexHull."""
    hull = ConvexHull(vertices)
    normals: list[list[float]] = []
    heights: list[float] = []

    for eq in hull.equations:
        normal = eq[:-1]
        offset = eq[-1]
        norm = np.linalg.norm(normal)
        if norm < 1e-10:
            continue
        normal = normal / norm
        offset = offset / norm
        height = -offset
        if height < 0:
            normal = -normal
            height = -height
        normals.append([float(x) for x in normal])
        heights.append(float(height))

    return normals, heights


def make_random_hull_python(
    n_points: int, rng: random.Random
) -> tuple[list[list[float]], list[float], int]:
    """Generate random convex hull in R^4 (for HK2017)."""
    points = np.array([[rng.uniform(-1, 1) for _ in range(4)] for _ in range(n_points)])
    centroid = points.mean(axis=0)
    points = points - centroid
    points = points * 1.5

    try:
        normals, heights = vertices_to_hrep(points)
        return normals, heights, len(normals)
    except Exception:
        return [], [], 0


# =============================================================================
# Timing Functions
# =============================================================================


def time_hk2017(
    normals: list[list[float]],
    heights: list[float],
    use_graph_pruning: bool = False,
) -> tuple[float, float, int, int]:
    """Time HK2017 capacity computation."""
    if ffi is None:
        raise RuntimeError("rust_viterbo_ffi not installed")

    start = time.perf_counter()
    result = ffi.hk2017_capacity_hrep(normals, heights, use_graph_pruning)
    elapsed = time.perf_counter() - start

    return (
        elapsed * 1000,  # ms
        result.capacity,
        result.permutations_evaluated,
        result.permutations_rejected,
    )


def time_tube(
    normals: list[list[float]],
    heights: list[float],
) -> tuple[float, float, int, int]:
    """Time tube capacity computation."""
    if ffi is None:
        raise RuntimeError("rust_viterbo_ffi not installed")

    start = time.perf_counter()
    result = ffi.tube_capacity_hrep(normals, heights)
    elapsed = time.perf_counter() - start

    return (
        elapsed * 1000,  # ms
        result.capacity,
        result.tubes_explored,
        result.tubes_pruned,
    )


# =============================================================================
# Benchmark Runner
# =============================================================================


def benchmark_polytope(
    polytope_id: str,
    family: str,
    normals: list[list[float]],
    heights: list[float],
    algorithms: list[str],
    n_reps: int,
    warmup: bool = True,
) -> list[BenchmarkResult]:
    """Benchmark a polytope with specified algorithms."""
    n_facets = len(normals)
    results: list[BenchmarkResult] = []

    for algo in algorithms:
        # Warmup
        if warmup:
            try:
                if algo in ("hk2017_naive", "hk2017_graph"):
                    time_hk2017(normals, heights, use_graph_pruning=(algo == "hk2017_graph"))
                elif algo == "tube":
                    time_tube(normals, heights)
            except Exception:
                pass  # Warmup errors are ok

        # Timed runs
        for rep in range(n_reps):
            try:
                if algo == "hk2017_naive":
                    wall_time, capacity, perms_eval, perms_rej = time_hk2017(
                        normals, heights, use_graph_pruning=False
                    )
                    results.append(
                        BenchmarkResult(
                            polytope_id=polytope_id,
                            polytope_family=family,
                            n_facets=n_facets,
                            algorithm=algo,
                            rep=rep,
                            wall_time_ms=wall_time,
                            capacity=capacity,
                            permutations_evaluated=perms_eval,
                            permutations_rejected=perms_rej,
                            tubes_explored=0,
                            tubes_pruned=0,
                            success=True,
                        )
                    )
                elif algo == "hk2017_graph":
                    wall_time, capacity, perms_eval, perms_rej = time_hk2017(
                        normals, heights, use_graph_pruning=True
                    )
                    results.append(
                        BenchmarkResult(
                            polytope_id=polytope_id,
                            polytope_family=family,
                            n_facets=n_facets,
                            algorithm=algo,
                            rep=rep,
                            wall_time_ms=wall_time,
                            capacity=capacity,
                            permutations_evaluated=perms_eval,
                            permutations_rejected=perms_rej,
                            tubes_explored=0,
                            tubes_pruned=0,
                            success=True,
                        )
                    )
                elif algo == "tube":
                    wall_time, capacity, tubes_expl, tubes_pr = time_tube(
                        normals, heights
                    )
                    results.append(
                        BenchmarkResult(
                            polytope_id=polytope_id,
                            polytope_family=family,
                            n_facets=n_facets,
                            algorithm=algo,
                            rep=rep,
                            wall_time_ms=wall_time,
                            capacity=capacity,
                            permutations_evaluated=0,
                            permutations_rejected=0,
                            tubes_explored=tubes_expl,
                            tubes_pruned=tubes_pr,
                            success=True,
                        )
                    )
            except Exception as e:
                results.append(
                    BenchmarkResult(
                        polytope_id=polytope_id,
                        polytope_family=family,
                        n_facets=n_facets,
                        algorithm=algo,
                        rep=rep,
                        wall_time_ms=0,
                        capacity=0,
                        permutations_evaluated=0,
                        permutations_rejected=0,
                        tubes_explored=0,
                        tubes_pruned=0,
                        success=False,
                        error=str(e),
                    )
                )

    return results


def run_benchmarks(cfg: dict[str, Any]) -> list[BenchmarkResult]:
    """Run the full benchmark suite."""
    results: list[BenchmarkResult] = []
    rng = random.Random(cfg["seed"])
    n_reps = cfg["repetitions"]

    # Fixed fixtures
    print("Benchmarking fixed fixtures...")

    # Tesseract (HK2017 only - has Lagrangian 2-faces)
    normals, heights = make_tesseract_hrep()
    results.extend(
        benchmark_polytope(
            "tesseract", "tesseract", normals, heights,
            ["hk2017_naive", "hk2017_graph"], n_reps
        )
    )
    print(f"  tesseract: {len(normals)} facets")

    # 4-simplex (HK2017 only - has Lagrangian 2-faces)
    normals, heights = make_simplex_hrep()
    results.extend(
        benchmark_polytope(
            "simplex", "simplex", normals, heights,
            ["hk2017_naive", "hk2017_graph"], n_reps
        )
    )
    print(f"  simplex: {len(normals)} facets")

    # Cross-polytope (Tube only - 16 facets is too many for HK2017)
    normals, heights = make_cross_polytope_hrep()
    results.extend(
        benchmark_polytope(
            "cross_polytope", "cross_polytope", normals, heights,
            ["tube"], n_reps
        )
    )
    print(f"  cross_polytope: {len(normals)} facets (tube only)")

    # 24-cell (Tube only - 24 facets is too many for HK2017)
    normals, heights = make_24_cell_hrep()
    results.extend(
        benchmark_polytope(
            "24_cell", "24_cell", normals, heights,
            ["tube"], n_reps
        )
    )
    print(f"  24_cell: {len(normals)} facets (tube only)")

    # Random polytopes for HK2017 (Python generation)
    print("\nGenerating random polytopes for HK2017...")
    hk2017_facet_counts = cfg.get("hk2017_facet_counts", [5, 8, 9, 10])
    max_attempts = cfg.get("max_random_attempts", 500)

    for target_facets in hk2017_facet_counts:
        count = 0
        n_points = target_facets + 2  # Rough heuristic
        attempts = 0

        while count < cfg["random_polytopes_per_facet"] and attempts < max_attempts:
            attempts += 1
            normals, heights, n_facets = make_random_hull_python(n_points, rng)

            if n_facets == target_facets:
                polytope_id = f"random_hk2017_f{target_facets}_s{count}"
                results.extend(
                    benchmark_polytope(
                        polytope_id, "random_hk2017", normals, heights,
                        ["hk2017_naive", "hk2017_graph"], n_reps
                    )
                )
                count += 1

        print(f"  {target_facets} facets: {count}/{cfg['random_polytopes_per_facet']} polytopes")

    # Random polytopes for Tube (FFI generation - filters for non-Lagrangian)
    print("\nGenerating random polytopes for Tube (via FFI)...")
    if ffi is None:
        raise RuntimeError("rust_viterbo_ffi not installed")

    tube_facet_counts = cfg.get("tube_facet_counts", [8, 10, 12, 14, 16])
    min_omega = cfg.get("min_omega", 0.01)

    for target_facets in tube_facet_counts:
        count = 0
        seed_offset = 0

        while count < cfg["random_polytopes_per_facet"]:
            seed_offset += 1
            if seed_offset > 10000:  # Safety limit
                print(f"    Warning: Could not find enough {target_facets}-facet polytopes")
                break

            result = ffi.random_hrep(target_facets, min_omega, cfg["seed"] + seed_offset)
            if result is None:
                continue

            normals, heights = result
            polytope_id = f"random_tube_f{target_facets}_s{count}"

            # Benchmark with all algorithms (HK2017 should work too)
            results.extend(
                benchmark_polytope(
                    polytope_id, "random_tube", normals, heights,
                    ["hk2017_naive", "hk2017_graph", "tube"], n_reps
                )
            )
            count += 1

        print(f"  {target_facets} facets: {count}/{cfg['random_polytopes_per_facet']} polytopes")

    return results


def load_config(path: Path) -> dict[str, Any]:
    """Load JSON config file."""
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def main(config_path: str = "config/runtime-performance-analysis/default.json") -> None:
    """Run benchmarks and save results."""
    cfg = load_config(Path(config_path))

    # Ensure output directory exists
    out_dir = Path(cfg["output_dir"])
    out_dir.mkdir(parents=True, exist_ok=True)

    print("Running runtime performance benchmarks")
    print(f"  Config: {config_path}")
    print(f"  Repetitions: {cfg['repetitions']}")
    print(f"  Random polytopes per facet count: {cfg['random_polytopes_per_facet']}")
    print()

    results = run_benchmarks(cfg)

    # Save results
    out_path = out_dir / "benchmark_results.json"
    with out_path.open("w", encoding="utf-8") as f:
        json.dump([asdict(r) for r in results], f, indent=2)

    print(f"\nWrote {len(results)} benchmark results to {out_path}")

    # Print summary
    successful = [r for r in results if r.success]
    print(f"Successful runs: {len(successful)}/{len(results)}")

    # Group by algorithm
    by_algo: dict[str, list[BenchmarkResult]] = {}
    for r in successful:
        by_algo.setdefault(r.algorithm, []).append(r)

    print("\nSummary by algorithm:")
    for algo in sorted(by_algo.keys()):
        runs = by_algo[algo]
        times = [r.wall_time_ms for r in runs]
        print(f"  {algo}: {len(runs)} runs, mean={np.mean(times):.2f}ms, std={np.std(times):.2f}ms")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Benchmark runtime performance")
    parser.add_argument(
        "--config",
        default="config/runtime-performance-analysis/default.json",
        help="Path to config file",
    )
    args = parser.parse_args()
    main(args.config)
