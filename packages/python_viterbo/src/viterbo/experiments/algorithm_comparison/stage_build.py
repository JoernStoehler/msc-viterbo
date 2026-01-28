"""Build stage: Run capacity algorithms on test polytopes and store results."""

import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import rust_viterbo_ffi as ffi


@dataclass
class AlgorithmResult:
    """Result from a single algorithm run."""

    algorithm: str
    capacity: float | None
    error: str | None
    metadata: dict


@dataclass
class ComparisonRecord:
    """Comparison record for a single polytope."""

    name: str
    polytope_type: str  # "lagrangian_product" or "general"
    results: list[AlgorithmResult]


def square_vertices(half_width: float) -> list[list[float]]:
    """Generate CCW vertices for a square centered at origin."""
    s = half_width
    return [[-s, -s], [s, -s], [s, s], [-s, s]]


def regular_polygon_vertices(n: int, circumradius: float) -> list[list[float]]:
    """Generate CCW vertices for a regular n-gon."""
    return [
        [circumradius * math.cos(2 * math.pi * k / n), circumradius * math.sin(2 * math.pi * k / n)]
        for k in range(n)
    ]


def rotated_vertices(vertices: list[list[float]], angle: float) -> list[list[float]]:
    """Rotate vertices by angle (radians) around origin."""
    c, s = math.cos(angle), math.sin(angle)
    return [[c * x - s * y, s * x + c * y] for x, y in vertices]


def lagrangian_product_to_hrep(
    vertices_q: list[list[float]], vertices_p: list[list[float]]
) -> tuple[list[list[float]], list[float]]:
    """Convert Lagrangian product K_q × K_p to H-rep for HK2017.

    For a Lagrangian product, each edge of K_q contributes a facet with normal
    (n_q, 0) and each edge of K_p contributes a facet with normal (0, n_p).
    """
    normals = []
    heights = []

    # Facets from K_q (in q1, q2 coordinates = first two of R^4)
    n_q = len(vertices_q)
    for i in range(n_q):
        v0 = vertices_q[i]
        v1 = vertices_q[(i + 1) % n_q]
        edge = [v1[0] - v0[0], v1[1] - v0[1]]
        # Outward normal (rotate edge 90° CW for CCW vertices)
        normal_2d = [edge[1], -edge[0]]
        length = math.sqrt(normal_2d[0] ** 2 + normal_2d[1] ** 2)
        normal_2d = [normal_2d[0] / length, normal_2d[1] / length]
        height = normal_2d[0] * v0[0] + normal_2d[1] * v0[1]
        # Embed in R^4: (n1, n2, 0, 0)
        normals.append([normal_2d[0], normal_2d[1], 0.0, 0.0])
        heights.append(height)

    # Facets from K_p (in p1, p2 coordinates = last two of R^4)
    n_p = len(vertices_p)
    for i in range(n_p):
        v0 = vertices_p[i]
        v1 = vertices_p[(i + 1) % n_p]
        edge = [v1[0] - v0[0], v1[1] - v0[1]]
        normal_2d = [edge[1], -edge[0]]
        length = math.sqrt(normal_2d[0] ** 2 + normal_2d[1] ** 2)
        normal_2d = [normal_2d[0] / length, normal_2d[1] / length]
        height = normal_2d[0] * v0[0] + normal_2d[1] * v0[1]
        # Embed in R^4: (0, 0, n1, n2)
        normals.append([0.0, 0.0, normal_2d[0], normal_2d[1]])
        heights.append(height)

    return normals, heights


def run_comparison(name: str, vertices_q: list, vertices_p: list) -> ComparisonRecord:
    """Run HK2017 and Billiard on a Lagrangian product."""
    results = []

    # Billiard
    try:
        r = ffi.billiard_capacity_polygons(vertices_q, vertices_p)
        results.append(
            AlgorithmResult(
                algorithm="billiard",
                capacity=r.capacity,
                error=None,
                metadata={"num_bounces": r.num_bounces, "combinations": r.combinations_evaluated},
            )
        )
    except Exception as e:
        results.append(AlgorithmResult(algorithm="billiard", capacity=None, error=str(e), metadata={}))

    # HK2017
    try:
        normals, heights = lagrangian_product_to_hrep(vertices_q, vertices_p)
        r = ffi.hk2017_capacity_hrep(normals, heights)
        results.append(
            AlgorithmResult(
                algorithm="hk2017",
                capacity=r.capacity,
                error=None,
                metadata={"permutations_evaluated": r.permutations_evaluated},
            )
        )
    except Exception as e:
        results.append(AlgorithmResult(algorithm="hk2017", capacity=None, error=str(e), metadata={}))

    return ComparisonRecord(name=name, polytope_type="lagrangian_product", results=results)


def main(output_dir: Path) -> None:
    """Run all comparisons and save results."""
    output_dir.mkdir(parents=True, exist_ok=True)
    records: list[ComparisonRecord] = []

    # === Lagrangian Products ===

    # Tesseract (square × square)
    square = square_vertices(1.0)
    records.append(run_comparison("tesseract", square, square))

    # Rectangle × Square
    rect = [[-1.0, -2.0], [1.0, -2.0], [1.0, 2.0], [-1.0, 2.0]]
    records.append(run_comparison("rectangle_x_square", rect, square))

    # Triangle × Triangle
    triangle = regular_polygon_vertices(3, 1.0)
    records.append(run_comparison("triangle_x_triangle", triangle, triangle))

    # Square × Triangle (asymmetric)
    records.append(run_comparison("square_x_triangle", square, triangle))

    # Small square × Large square
    small_square = square_vertices(0.5)
    large_square = square_vertices(2.0)
    records.append(run_comparison("small_x_large_square", small_square, large_square))

    # Pentagon × Rotated Pentagon (HK-O 2024 counterexample)
    pentagon = regular_polygon_vertices(5, 1.0)
    rotated_pentagon = rotated_vertices(pentagon, math.pi / 2)
    records.append(run_comparison("pentagon_counterexample", pentagon, rotated_pentagon))

    # === Save Results ===
    output_file = output_dir / "results.json"
    with open(output_file, "w") as f:
        json.dump([asdict(r) for r in records], f, indent=2)

    print(f"Saved {len(records)} comparison records to {output_file}")

    # Print summary
    print("\n=== Summary ===")
    for record in records:
        caps = {r.algorithm: r.capacity for r in record.results if r.capacity is not None}
        if len(caps) == 2:
            b, h = caps.get("billiard"), caps.get("hk2017")
            if b and h:
                ratio = b / h
                agree = abs(ratio - 1.0) < 0.01
                status = "AGREE" if agree else f"DISAGREE (ratio={ratio:.4f})"
                print(f"{record.name}: billiard={b:.4f}, hk2017={h:.4f} -> {status}")
        else:
            print(f"{record.name}: incomplete ({caps})")


if __name__ == "__main__":
    import sys

    if len(sys.argv) > 1:
        output_dir = Path(sys.argv[1])
    else:
        output_dir = Path(__file__).parent.parent.parent.parent.parent / "data" / "algorithm-comparison"
    main(output_dir)
