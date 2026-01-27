"""Stage 1: Generate polytopes and time HK2017 execution.

This stage:
1. Generates polytopes from various families (simplex, tesseract, random hulls)
2. Times HK2017 capacity computation on each
3. Saves timing data to JSON

Usage:
    uv run python -m viterbo.experiments.benchmark_hk2017.stage_build
    uv run python -m viterbo.experiments.benchmark_hk2017.stage_build --config config/benchmark-hk2017/quick.json
"""

from __future__ import annotations

import argparse
import json
import math
import random
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any

import numpy as np
from scipy.spatial import ConvexHull

# Conditional import for FFI
try:
    import rust_viterbo_ffi as ffi
except ImportError:
    ffi = None


@dataclass
class TimingResult:
    """Result of timing a single HK2017 run."""

    family: str
    n_facets: int
    n_points: int  # For random hulls; 0 for fixed polytopes
    rep: int
    algorithm: str  # "naive" or "graph_pruned"
    wall_time_ms: float
    capacity: float
    permutations_evaluated: int
    permutations_rejected: int
    success: bool
    error: str | None = None


def load_config(path: Path) -> dict[str, Any]:
    """Load JSON config file."""
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def make_simplex_hrep() -> tuple[list[tuple[float, float, float, float]], list[float]]:
    """Create 4D simplex containing origin, in H-representation.

    Returns unit outward normals and positive heights.
    The simplex has 5 facets.

    We use a simple construction: 5 hyperplanes that define a simplex
    containing the origin. The normals point in the directions of the
    vertices of a dual simplex.
    """
    # Use a simple axis-aligned approach that's known to work
    # 5 facets with normals pointing roughly toward standard simplex vertices
    # but ensuring origin is inside

    # For a valid H-rep, we need:
    # 1. Unit normals
    # 2. Positive heights (origin inside)

    # Simple 5-facet simplex: one facet for each coordinate direction plus one "closing" facet
    s = 1.0 / math.sqrt(4)  # = 0.5
    diag_norm = math.sqrt(4 * s * s)  # = 1
    normals: list[tuple[float, float, float, float]] = [
        (1.0, 0.0, 0.0, 0.0),  # +x
        (0.0, 1.0, 0.0, 0.0),  # +y
        (0.0, 0.0, 1.0, 0.0),  # +z
        (0.0, 0.0, 0.0, 1.0),  # +w
        (-s / diag_norm, -s / diag_norm, -s / diag_norm, -s / diag_norm),  # -diagonal
    ]

    # Heights: distance from origin to each facet
    # For the axis-aligned facets, use height 1
    # For the diagonal facet, we need to ensure it's positive
    heights = [1.0, 1.0, 1.0, 1.0, 0.5]  # diagonal closer to origin

    return normals, heights


def make_tesseract_hrep() -> tuple[list[tuple[float, float, float, float]], list[float]]:
    """Create tesseract [-1, 1]^4 in H-representation.

    Returns unit outward normals and positive heights.
    The tesseract has 8 facets.
    """
    normals: list[tuple[float, float, float, float]] = [
        (1.0, 0.0, 0.0, 0.0),
        (-1.0, 0.0, 0.0, 0.0),
        (0.0, 1.0, 0.0, 0.0),
        (0.0, -1.0, 0.0, 0.0),
        (0.0, 0.0, 1.0, 0.0),
        (0.0, 0.0, -1.0, 0.0),
        (0.0, 0.0, 0.0, 1.0),
        (0.0, 0.0, 0.0, -1.0),
    ]
    heights = [1.0] * 8
    return normals, heights


def vertices_to_hrep(
    vertices: np.ndarray,
) -> tuple[list[tuple[float, float, float, float]], list[float]]:
    """Convert V-representation to H-representation.

    Args:
        vertices: (N, 4) array of vertex coordinates

    Returns:
        (normals, heights) where normals are unit outward normals
        and heights are positive (origin assumed inside).
    """
    hull = ConvexHull(vertices)

    normals: list[tuple[float, float, float, float]] = []
    heights: list[float] = []

    for eq in hull.equations:
        # eq is [a, b, c, d, e] where a*x + b*y + c*z + d*w + e = 0
        # Normal is (a, b, c, d), offset is e
        normal = eq[:-1]
        offset = eq[-1]

        # Normalize
        norm = np.linalg.norm(normal)
        if norm < 1e-10:
            continue

        normal = normal / norm
        offset = offset / norm

        # Height = distance from origin to hyperplane = -offset (if normal points outward)
        # ConvexHull equations point inward, so we negate
        height = -offset

        if height < 0:
            # Flip normal to point outward
            normal = -normal
            height = -height

        normals.append((float(normal[0]), float(normal[1]), float(normal[2]), float(normal[3])))
        heights.append(float(height))

    return normals, heights


def make_random_hull(
    n_points: int, rng: random.Random
) -> tuple[list[tuple[float, float, float, float]], list[float], int]:
    """Generate random convex hull in R^4.

    Args:
        n_points: Number of random points to generate
        rng: Random number generator

    Returns:
        (normals, heights, n_facets) tuple
    """
    # Generate points uniformly in [-1, 1]^4, then shift to ensure origin is inside
    points = np.array([[rng.uniform(-1, 1) for _ in range(4)] for _ in range(n_points)])

    # Shift points so centroid is at origin (ensures origin is inside hull)
    centroid = points.mean(axis=0)
    points = points - centroid

    # Scale to ensure some margin
    points = points * 1.5

    try:
        normals, heights = vertices_to_hrep(points)
        return normals, heights, len(normals)
    except Exception:
        return [], [], 0


def time_hk2017(
    normals: list[tuple[float, float, float, float]],
    heights: list[float],
    use_graph_pruning: bool = False,
) -> tuple[float, float, int, int]:
    """Time HK2017 capacity computation.

    Args:
        normals: Unit outward normal vectors.
        heights: Distances from origin to facets.
        use_graph_pruning: If True, use graph-based cycle enumeration.

    Returns:
        (wall_time_ms, capacity, perms_evaluated, perms_rejected)
    """
    if ffi is None:
        raise RuntimeError(
            "rust_viterbo_ffi not installed. Build with: "
            "cd packages/python_viterbo && uv run maturin develop "
            "--manifest-path ../rust_viterbo/ffi/Cargo.toml"
        )

    start = time.perf_counter()
    result = ffi.hk2017_capacity_hrep(normals, heights, use_graph_pruning)
    elapsed = time.perf_counter() - start

    return (
        elapsed * 1000,  # ms
        result.capacity,
        result.permutations_evaluated,
        result.permutations_rejected,
    )


def _time_polytope(
    family: str,
    n_facets: int,
    n_points: int,
    rep: int,
    normals: list[tuple[float, float, float, float]],
    heights: list[float],
    algorithms: list[str],
) -> list[TimingResult]:
    """Time a single polytope with all specified algorithms."""
    results = []
    for algo in algorithms:
        use_graph_pruning = algo == "graph_pruned"
        try:
            wall_time, capacity, evaluated, rejected = time_hk2017(
                normals, heights, use_graph_pruning
            )
            results.append(
                TimingResult(
                    family=family,
                    n_facets=n_facets,
                    n_points=n_points,
                    rep=rep,
                    algorithm=algo,
                    wall_time_ms=wall_time,
                    capacity=capacity,
                    permutations_evaluated=evaluated,
                    permutations_rejected=rejected,
                    success=True,
                )
            )
        except Exception as e:
            results.append(
                TimingResult(
                    family=family,
                    n_facets=n_facets,
                    n_points=n_points,
                    rep=rep,
                    algorithm=algo,
                    wall_time_ms=0,
                    capacity=0,
                    permutations_evaluated=0,
                    permutations_rejected=0,
                    success=False,
                    error=str(e),
                )
            )
    return results


def run_benchmark(cfg: dict[str, Any]) -> list[TimingResult]:
    """Run the full benchmark suite."""
    rng = random.Random(cfg["seed"])
    results: list[TimingResult] = []

    facet_counts = cfg["facet_counts"]
    reps = cfg["repetitions"]
    algorithms = cfg.get("algorithms", ["naive", "graph_pruned"])

    print(f"Testing algorithms: {algorithms}")

    # 1. Benchmark tesseract (8 facets) - known to work, capacity = 4.0
    if 8 in facet_counts:
        print("Benchmarking tesseract (8 facets)...")
        normals, heights = make_tesseract_hrep()
        for rep in range(reps):
            results.extend(
                _time_polytope("tesseract", 8, 0, rep, normals, heights, algorithms)
            )

    # 2. Benchmark random hulls
    # In 4D: 5 points -> 5 facets (simplex), 6-7 points -> 8-10 facets
    print("Benchmarking random hulls...")
    max_attempts = cfg.get("max_random_attempts", 500)

    # Exclude 8 facets since we already have tesseract
    target_facets = [f for f in facet_counts if f != 8]
    # Track count per facet (independent of algorithm)
    polytope_count_by_facets: dict[int, int] = {f: 0 for f in target_facets}

    # For 5 facets, use exactly 5 points (always gives simplex)
    if 5 in target_facets:
        print("  Generating 5-facet simplices (5 points)...")
        for rep in range(reps):
            normals, heights, n_facets = make_random_hull(5, rng)
            if n_facets != 5:
                continue
            results.extend(
                _time_polytope("random_simplex", 5, 5, rep, normals, heights, algorithms)
            )
            polytope_count_by_facets[5] += 1
        print(f"    Got {polytope_count_by_facets[5]}/{reps} polytopes")

    # For 8-10 facets, use 6-7 points
    other_targets = [f for f in target_facets if f != 5]
    if other_targets:
        print(f"  Generating {other_targets} facet polytopes (6-7 points)...")
        attempts = 0
        while attempts < max_attempts:
            attempts += 1
            n_points = rng.choice([6, 7])
            normals, heights, n_facets = make_random_hull(n_points, rng)

            if n_facets == 0 or n_facets not in polytope_count_by_facets:
                continue
            if polytope_count_by_facets[n_facets] >= reps:
                continue

            rep = polytope_count_by_facets[n_facets]
            results.extend(
                _time_polytope("random_hull", n_facets, n_points, rep, normals, heights, algorithms)
            )
            polytope_count_by_facets[n_facets] += 1

            if all(polytope_count_by_facets[f] >= reps for f in other_targets):
                break

    # Print summary
    for f in sorted(polytope_count_by_facets.keys()):
        if f != 5:  # Already printed
            print(f"    {f} facets: {polytope_count_by_facets[f]}/{reps} polytopes")

    return results


def main(config_path: str = "config/benchmark-hk2017/default.json") -> None:
    """Run benchmark and save results."""
    cfg = load_config(Path(config_path))

    # Ensure output directory exists
    out_dir = Path(cfg["output_dir"])
    out_dir.mkdir(parents=True, exist_ok=True)

    print(f"Running HK2017 benchmark with config: {config_path}")
    print(f"Facet counts: {cfg['facet_counts']}")
    print(f"Repetitions: {cfg['repetitions']}")

    results = run_benchmark(cfg)

    # Save results
    out_path = out_dir / "timings.json"
    with out_path.open("w", encoding="utf-8") as f:
        json.dump([asdict(r) for r in results], f, indent=2)

    print(f"\nWrote {len(results)} timing results to {out_path}")

    # Print summary
    successful = [r for r in results if r.success]
    print(f"Successful runs: {len(successful)}/{len(results)}")

    if successful:
        by_facets: dict[int, list[float]] = {}
        for r in successful:
            by_facets.setdefault(r.n_facets, []).append(r.wall_time_ms)

        print("\nMean times by facet count:")
        for f in sorted(by_facets.keys()):
            times = by_facets[f]
            mean_ms = sum(times) / len(times)
            print(f"  {f} facets: {mean_ms:.2f} ms (n={len(times)})")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Benchmark HK2017 algorithm")
    parser.add_argument(
        "--config",
        default="config/benchmark-hk2017/default.json",
        help="Path to config file",
    )
    args = parser.parse_args()
    main(args.config)
