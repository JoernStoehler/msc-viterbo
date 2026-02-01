"""Stage 1: Generate polytope geometries only.

This stage generates polytope H-representations without computing capacities or volumes.
Output contains only geometric data (normals, heights) and basic properties.

Usage:
    uv run python -m viterbo.experiments.polytope_database.stage_polytopes

Output:
    data/polytope-database/polytopes.json
"""

from __future__ import annotations

import json
import math
import random
from pathlib import Path


def tesseract_hrep() -> tuple[list[list[float]], list[float]]:
    """H-rep for tesseract [-1,1]^4. Known capacity = 4.0."""
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


def simplex_hrep() -> tuple[list[list[float]], list[float]]:
    """H-rep for regular 4-simplex centered at origin. Known capacity = 0.25."""
    # 5 facets pointing toward vertices of a regular simplex
    sqrt5 = math.sqrt(5)
    normals = [
        [1.0, 1.0, 1.0, -1.0 / sqrt5],
        [1.0, -1.0, -1.0, -1.0 / sqrt5],
        [-1.0, 1.0, -1.0, -1.0 / sqrt5],
        [-1.0, -1.0, 1.0, -1.0 / sqrt5],
        [0.0, 0.0, 0.0, 4.0 / sqrt5],
    ]
    # Normalize to unit vectors
    for i, n in enumerate(normals):
        norm = math.sqrt(sum(x * x for x in n))
        normals[i] = [x / norm for x in n]
    heights = [0.5] * 5  # Scaled so 0 is in interior
    return normals, heights


def cross_polytope_hrep() -> tuple[list[list[float]], list[float]]:
    """H-rep for cross-polytope (orthoplex) conv(±e_i).

    The cross-polytope is the dual of the tesseract. It has 16 facets
    with normals (±1, ±1, ±1, ±1)/2.
    """
    normals = []
    for s1 in [-1, 1]:
        for s2 in [-1, 1]:
            for s3 in [-1, 1]:
                for s4 in [-1, 1]:
                    normals.append([s1 / 2, s2 / 2, s3 / 2, s4 / 2])
    heights = [0.5] * 16
    return normals, heights


def cell_24_hrep() -> tuple[list[list[float]], list[float]]:
    """H-rep for 24-cell (icositetrachoron).

    A regular 4D polytope with 24 octahedral cells. Self-dual.

    Properties:
    - 24 facets with normals (±1,±1,0,0)/√2 and permutations
    - All 2-faces are non-Lagrangian (suitable for tube algorithm)
    """
    s = 1.0 / math.sqrt(2)  # 1/√2 for unit normals
    normals = []

    # 24 normals: all permutations of (±1,±1,0,0)/√2
    # There are 6 coordinate pairs × 4 sign combinations = 24 normals
    pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

    for i, j in pairs:
        for s1 in [-1.0, 1.0]:
            for s2 in [-1.0, 1.0]:
                n = [0.0, 0.0, 0.0, 0.0]
                n[i] = s1 * s
                n[j] = s2 * s
                normals.append(n)

    # Heights: for the unit 24-cell, h = 1/√2
    heights = [s] * 24
    return normals, heights


def random_hrep(n_facets: int, seed: int) -> tuple[list[list[float]], list[float]]:
    """Generate random H-rep with n_facets facets."""
    rng = random.Random(seed)
    normals = []
    for _ in range(n_facets):
        # Random unit normal
        v = [rng.gauss(0, 1) for _ in range(4)]
        norm = math.sqrt(sum(x * x for x in v))
        normals.append([x / norm for x in v])
    # Heights all positive (0 in interior)
    heights = [rng.uniform(0.5, 2.0) for _ in range(n_facets)]
    return normals, heights


def is_lagrangian_product(normals: list[list[float]]) -> bool:
    """Check if polytope is a Lagrangian product K1 x K2.

    A Lagrangian product has all normals of form (n_q, 0) or (0, n_p).
    """
    for n in normals:
        q_part = n[0] ** 2 + n[1] ** 2
        p_part = n[2] ** 2 + n[3] ** 2
        # Either q-only or p-only (with tolerance)
        if not (q_part < 1e-10 or p_part < 1e-10):
            return False
    return True


def has_lagrangian_2face(normals: list[list[float]]) -> bool:
    """Check if polytope has any Lagrangian 2-face.

    A 2-face F_ij is Lagrangian iff omega(n_i, n_j) = 0.
    omega(x, y) = x[0]*y[2] + x[1]*y[3] - x[2]*y[0] - x[3]*y[1]
    """
    n = len(normals)
    for i in range(n):
        for j in range(i + 1, n):
            ni, nj = normals[i], normals[j]
            omega = ni[0] * nj[2] + ni[1] * nj[3] - ni[2] * nj[0] - ni[3] * nj[1]
            if abs(omega) < 1e-9:
                return True
    return False


def generate_polytopes() -> list[dict]:
    """Generate polytope geometries without capacity or volume data."""
    polytopes = []

    # Tesseract
    normals, heights = tesseract_hrep()
    polytopes.append(
        {
            "id": "tesseract",
            "family": "tesseract",
            "facet_count": len(normals),
            "normals": normals,
            "heights": heights,
            "has_lagrangian_2face": has_lagrangian_2face(normals),
            "is_lagrangian_product": is_lagrangian_product(normals),
        }
    )

    # 4-Simplex
    normals, heights = simplex_hrep()
    polytopes.append(
        {
            "id": "simplex",
            "family": "simplex",
            "facet_count": len(normals),
            "normals": normals,
            "heights": heights,
            "has_lagrangian_2face": has_lagrangian_2face(normals),
            "is_lagrangian_product": is_lagrangian_product(normals),
        }
    )

    # Cross-polytope
    normals, heights = cross_polytope_hrep()
    polytopes.append(
        {
            "id": "cross-polytope",
            "family": "cross-polytope",
            "facet_count": len(normals),
            "normals": normals,
            "heights": heights,
            "has_lagrangian_2face": has_lagrangian_2face(normals),
            "is_lagrangian_product": is_lagrangian_product(normals),
        }
    )

    # 24-cell
    normals, heights = cell_24_hrep()
    polytopes.append(
        {
            "id": "24-cell",
            "family": "24-cell",
            "facet_count": len(normals),
            "normals": normals,
            "heights": heights,
            "has_lagrangian_2face": has_lagrangian_2face(normals),
            "is_lagrangian_product": is_lagrangian_product(normals),
        }
    )

    # Random polytopes
    for i in range(8):
        seed = 100 + i
        n_facets = random.Random(seed).randint(6, 12)
        normals, heights = random_hrep(n_facets, seed)
        polytopes.append(
            {
                "id": f"random-{i:03d}",
                "family": "random",
                "facet_count": len(normals),
                "normals": normals,
                "heights": heights,
                "has_lagrangian_2face": has_lagrangian_2face(normals),
                "is_lagrangian_product": is_lagrangian_product(normals),
            }
        )

    return polytopes


def main(data_dir: Path | None = None) -> None:
    """Generate polytopes and save to JSON.

    Args:
        data_dir: Output directory. If None, uses default data directory.
    """
    if data_dir is None:
        from viterbo.paths import get_data_dir
        data_dir = get_data_dir("polytope-database")

    polytopes = generate_polytopes()

    # Ensure output directory exists
    data_dir.mkdir(parents=True, exist_ok=True)

    out_path = data_dir / "polytopes.json"
    with open(out_path, "w") as f:
        json.dump(polytopes, f, indent=2)

    print(f"Wrote {len(polytopes)} polytopes to {out_path}")
    print(f"Families: {set(p['family'] for p in polytopes)}")
    print(f"Facet counts: {sorted(set(p['facet_count'] for p in polytopes))}")


if __name__ == "__main__":
    main()
