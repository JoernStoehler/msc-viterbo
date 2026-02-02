"""Build stage: Run capacity algorithms on test polytopes and store results.

Data format: Each row is a polytope with columns for:
- Geometry (name, type, vertices, facet count)
- Literature value (if known)
- Algorithm results (capacity, walltime, error)
"""

import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path

import rust_viterbo_ffi as ffi


@dataclass
class PolytopeRecord:
    """One row in the comparison dataset."""

    # Geometry
    name: str
    polytope_type: str  # "lagrangian_product"
    vertices_q: list[list[float]]
    vertices_p: list[list[float]]
    facet_count: int  # n_q + n_p for Lagrangian products

    # Literature
    literature_capacity: float | None
    literature_source: str | None

    # Billiard results
    billiard_capacity: float | None = None
    billiard_error: str | None = None
    billiard_walltime_ms: float | None = None
    billiard_num_bounces: int | None = None

    # HK2017 results
    hk2017_capacity: float | None = None
    hk2017_error: str | None = None
    hk2017_walltime_ms: float | None = None
    hk2017_permutations: int | None = None

    # Tube results (N/A for Lagrangian products - they have Lagrangian 2-faces)
    tube_capacity: float | None = None
    tube_error: str | None = "N/A for Lagrangian products"
    tube_walltime_ms: float | None = None


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
    """Convert Lagrangian product K_q × K_p to H-rep for HK2017."""
    normals = []
    heights = []

    for verts, embed in [(vertices_q, lambda n: [n[0], n[1], 0.0, 0.0]),
                          (vertices_p, lambda n: [0.0, 0.0, n[0], n[1]])]:
        n_v = len(verts)
        for i in range(n_v):
            v0, v1 = verts[i], verts[(i + 1) % n_v]
            edge = [v1[0] - v0[0], v1[1] - v0[1]]
            normal_2d = [edge[1], -edge[0]]
            length = math.sqrt(normal_2d[0] ** 2 + normal_2d[1] ** 2)
            normal_2d = [normal_2d[0] / length, normal_2d[1] / length]
            height = normal_2d[0] * v0[0] + normal_2d[1] * v0[1]
            normals.append(embed(normal_2d))
            heights.append(height)

    return normals, heights


def run_algorithms(record: PolytopeRecord) -> None:
    """Run billiard and HK2017 on a Lagrangian product, updating record in place."""
    # Billiard - not yet implemented in FFI (billiard crate is draft status)
    record.billiard_error = "Not yet implemented"

    # HK2017
    try:
        normals, heights = lagrangian_product_to_hrep(record.vertices_q, record.vertices_p)
        start = time.perf_counter()
        r = ffi.hk2017_capacity_hrep(normals, heights)
        record.hk2017_walltime_ms = (time.perf_counter() - start) * 1000
        record.hk2017_capacity = r.capacity
        record.hk2017_permutations = r.permutations_evaluated
    except Exception as e:
        record.hk2017_error = str(e)


def main(output_dir: Path) -> None:
    """Run all comparisons and save results."""
    output_dir.mkdir(parents=True, exist_ok=True)
    records: list[PolytopeRecord] = []

    # === Fixed test cases with literature values ===

    # Tesseract: known capacity = 4.0 (HK2017 Example 4.6)
    square = square_vertices(1.0)
    records.append(PolytopeRecord(
        name="tesseract",
        polytope_type="lagrangian_product",
        vertices_q=square,
        vertices_p=square,
        facet_count=8,
        literature_capacity=4.0,
        literature_source="HK2017 Example 4.6",
    ))

    # Pentagon counterexample: known capacity ≈ 3.441 (HK-O 2024)
    pentagon = regular_polygon_vertices(5, 1.0)
    rotated_pentagon = rotated_vertices(pentagon, math.pi / 2)
    expected_pentagon = 2 * math.cos(math.pi / 10) * (1 + math.cos(math.pi / 5))
    records.append(PolytopeRecord(
        name="pentagon_counterexample",
        polytope_type="lagrangian_product",
        vertices_q=pentagon,
        vertices_p=rotated_pentagon,
        facet_count=10,
        literature_capacity=expected_pentagon,
        literature_source="HK-O 2024 Theorem 1.1",
    ))

    # === Fixed test cases without literature values ===
    # (first idea accepted - no systematic evaluation of alternatives)

    # Rectangle × Square
    rect = [[-1.0, -2.0], [1.0, -2.0], [1.0, 2.0], [-1.0, 2.0]]
    records.append(PolytopeRecord(
        name="rectangle_x_square",
        polytope_type="lagrangian_product",
        vertices_q=rect,
        vertices_p=square,
        facet_count=8,
        literature_capacity=None,
        literature_source=None,
    ))

    # Triangle × Triangle
    triangle = regular_polygon_vertices(3, 1.0)
    records.append(PolytopeRecord(
        name="triangle_x_triangle",
        polytope_type="lagrangian_product",
        vertices_q=triangle,
        vertices_p=triangle,
        facet_count=6,
        literature_capacity=None,
        literature_source=None,
    ))

    # Square × Triangle
    records.append(PolytopeRecord(
        name="square_x_triangle",
        polytope_type="lagrangian_product",
        vertices_q=square,
        vertices_p=triangle,
        facet_count=7,
        literature_capacity=None,
        literature_source=None,
    ))

    # === Random Lagrangian products ===
    # (added after user feedback - no systematic evaluation of sampling strategy)
    import random
    for seed in range(20):
        random.seed(seed)
        n, m = random.randint(3, 6), random.randint(3, 6)
        r_q, r_p = 0.5 + random.random(), 0.5 + random.random()
        rot_q, rot_p = random.random() * 2 * math.pi, random.random() * 2 * math.pi

        poly_q = rotated_vertices(regular_polygon_vertices(n, r_q), rot_q)
        poly_p = rotated_vertices(regular_polygon_vertices(m, r_p), rot_p)

        records.append(PolytopeRecord(
            name=f"random_{seed}_{n}gon_x_{m}gon",
            polytope_type="lagrangian_product",
            vertices_q=poly_q,
            vertices_p=poly_p,
            facet_count=n + m,
            literature_capacity=None,
            literature_source=None,
        ))

    # === Run algorithms ===
    for record in records:
        run_algorithms(record)

    # === Save results ===
    output_file = output_dir / "results.json"
    with open(output_file, "w") as f:
        json.dump([asdict(r) for r in records], f, indent=2)

    print(f"Saved {len(records)} records to {output_file}")

    # === Print summary ===
    print("\n=== Summary ===")
    print(f"{'Name':<30} {'Lit.':<8} {'Billiard':<10} {'HK2017':<10} {'Status'}")
    print("-" * 75)

    for r in records:
        lit = f"{r.literature_capacity:.4f}" if r.literature_capacity else "N/A"
        bil = f"{r.billiard_capacity:.4f}" if r.billiard_capacity else "ERR"
        hk = f"{r.hk2017_capacity:.4f}" if r.hk2017_capacity else "ERR"

        if r.billiard_capacity and r.hk2017_capacity:
            ratio = r.billiard_capacity / r.hk2017_capacity
            status = "AGREE" if abs(ratio - 1.0) < 0.01 else f"DISAGREE ({ratio:.2f}x)"
        else:
            status = "INCOMPLETE"

        print(f"{r.name:<30} {lit:<8} {bil:<10} {hk:<10} {status}")


if __name__ == "__main__":
    import sys
    from viterbo.paths import get_data_dir
    output_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else get_data_dir("algorithm-comparison")
    main(output_dir)
