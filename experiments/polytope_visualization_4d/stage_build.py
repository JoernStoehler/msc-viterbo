"""Stage: Build polytope geometry from H-representation.

Converts H-rep to V-rep, extracts face structure, and computes projections.

Run:
    uv run python -m viterbo.experiments.polytope_visualization_4d.stage_build
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from itertools import combinations
from typing import Sequence

import numpy as np
from numpy.typing import NDArray
from scipy.optimize import linprog
from scipy.spatial import ConvexHull


# =============================================================================
# Projection Utilities
# =============================================================================


def radial_project_to_s3(
    v: NDArray[np.floating],
    *,
    epsilon: float = 1e-12,
) -> NDArray[np.floating]:
    """Project a 4D point onto S³ via radial projection.

    Maps v ∈ R⁴ to v/|v| ∈ S³.

    Args:
        v: 4D point as shape (4,) array
        epsilon: Minimum norm to avoid division by zero

    Returns:
        Unit 4D vector on S³

    Raises:
        ValueError: If point is too close to origin
    """
    norm = np.linalg.norm(v)
    if norm < epsilon:
        raise ValueError(f"Point too close to origin (norm={norm:.2e})")
    return v / norm


def stereographic_s3_to_r3(
    v: NDArray[np.floating],
    *,
    pole: int = 3,
    epsilon: float = 1e-10,
) -> NDArray[np.floating]:
    """Stereographic projection from S³ to R³.

    Projects from the 3-sphere in R⁴ to R³. The projection is done from
    a pole (by default, the positive w-axis pole at (0,0,0,1)).

    For a point (x, y, z, w) on S³, the stereographic projection is:
        (x/(1-w), y/(1-w), z/(1-w))

    This is conformal (preserves angles) but maps circles to circles/lines.

    Args:
        v: Point on S³ as shape (4,) array (must have |v| ≈ 1)
        pole: Index of coordinate to project from (default 3 = w-axis)
        epsilon: Tolerance for near-pole detection

    Returns:
        3D point in R³
    """
    pole_coord = v[pole]

    # Handle near-pole case (maps to "infinity")
    if 1 - pole_coord < epsilon:
        scale = 1e6
        coords_3d = np.array([v[i] for i in range(4) if i != pole])
        return coords_3d * scale

    # Standard stereographic formula
    denom = 1 - pole_coord
    coords_3d = np.array([v[i] / denom for i in range(4) if i != pole])

    return coords_3d


def project_4d_to_3d(
    v: NDArray[np.floating],
    *,
    pole: int = 3,
    epsilon: float = 1e-12,
) -> NDArray[np.floating]:
    """Combined radial + stereographic projection: R⁴ → R³.

    Args:
        v: 4D point as shape (4,) array
        pole: Stereographic pole index (default 3 = w-axis)
        epsilon: Tolerance for near-zero norms

    Returns:
        3D point in R³
    """
    v_s3 = radial_project_to_s3(v, epsilon=epsilon)
    return stereographic_s3_to_r3(v_s3, pole=pole, epsilon=epsilon)


def project_4d_points(
    points: NDArray[np.floating],
    *,
    pole: int = 3,
    epsilon: float = 1e-12,
) -> NDArray[np.floating]:
    """Project multiple 4D points to 3D.

    Args:
        points: Array of shape (n, 4)
        pole: Stereographic pole index
        epsilon: Tolerance

    Returns:
        Array of shape (n, 3)
    """
    n = points.shape[0]
    result = np.zeros((n, 3), dtype=points.dtype)
    for i in range(n):
        result[i] = project_4d_to_3d(points[i], pole=pole, epsilon=epsilon)
    return result


def interpolate_4d_segment(
    start: NDArray[np.floating],
    end: NDArray[np.floating],
    n_samples: int = 20,
) -> NDArray[np.floating]:
    """Interpolate along a 4D line segment.

    Args:
        start: Starting 4D point
        end: Ending 4D point
        n_samples: Number of sample points

    Returns:
        Array of shape (n_samples, 4)
    """
    t = np.linspace(0, 1, n_samples)[:, np.newaxis]
    return start + t * (end - start)


def project_4d_segment_to_3d(
    start: NDArray[np.floating],
    end: NDArray[np.floating],
    *,
    n_samples: int = 20,
    pole: int = 3,
) -> NDArray[np.floating]:
    """Project a 4D line segment to a 3D curve.

    Args:
        start: Starting 4D point
        end: Ending 4D point
        n_samples: Number of samples
        pole: Stereographic pole

    Returns:
        Array of shape (n_samples, 3)
    """
    segment_4d = interpolate_4d_segment(start, end, n_samples)
    return project_4d_points(segment_4d, pole=pole)


# =============================================================================
# Polytope Geometry
# =============================================================================


@dataclass
class PolytopeGeometry:
    """Complete geometric description of a 4D polytope.

    Attributes:
        normals: Facet normal vectors, shape (n_facets, 4)
        heights: Facet heights, shape (n_facets,)
        vertices: Vertex coordinates, shape (n_vertices, 4)
        facet_vertices: List of vertex indices for each facet
        edges: List of (i, j) vertex index pairs
        faces_2d: List of vertex index lists for each 2-face
    """

    normals: NDArray[np.floating]
    heights: NDArray[np.floating]
    vertices: NDArray[np.floating]
    facet_vertices: list[list[int]]
    edges: list[tuple[int, int]]
    faces_2d: list[list[int]]


def hrep_to_vertices(
    normals: NDArray[np.floating],
    heights: NDArray[np.floating],
    *,
    tol: float = 1e-9,
) -> NDArray[np.floating]:
    """Convert H-representation to V-representation (vertices).

    The polytope is defined as K = {x : n_i · x <= h_i} for all i.

    Args:
        normals: Facet normal vectors, shape (n_facets, 4)
        heights: Facet heights, shape (n_facets,)
        tol: Tolerance for feasibility checking

    Returns:
        Vertex coordinates, shape (n_vertices, 4)
    """
    n_facets = normals.shape[0]
    vertices = []

    # In 4D, vertices are intersections of exactly 4 hyperplanes
    for facet_indices in combinations(range(n_facets), 4):
        A = normals[list(facet_indices)]
        b = heights[list(facet_indices)]

        try:
            x = np.linalg.solve(A, b)
        except np.linalg.LinAlgError:
            continue

        # Check if solution is feasible
        if np.all(normals @ x <= heights + tol):
            # Check if new
            is_new = True
            for v in vertices:
                if np.linalg.norm(x - v) < tol:
                    is_new = False
                    break
            if is_new:
                vertices.append(x)

    if len(vertices) == 0:
        raise ValueError("No vertices found - check H-representation")

    return np.array(vertices)


def _find_interior_point(
    normals: NDArray[np.floating],
    heights: NDArray[np.floating],
) -> NDArray[np.floating]:
    """Find a strictly interior point of the polytope using LP."""
    n_facets = normals.shape[0]

    c = np.zeros(5)
    c[4] = -1  # Maximize s

    A_ub = np.hstack([normals, np.ones((n_facets, 1))])
    b_ub = heights

    result = linprog(c, A_ub=A_ub, b_ub=b_ub, method="highs")

    if not result.success or result.x is None:
        raise ValueError("Could not find interior point")

    return result.x[:4]


def _vertices_on_facet(
    vertices: NDArray[np.floating],
    normal: NDArray[np.floating],
    height: float,
    tol: float = 1e-9,
) -> list[int]:
    """Find indices of vertices lying on a facet."""
    dots = vertices @ normal
    return [i for i, d in enumerate(dots) if abs(d - height) < tol]


def extract_faces(
    normals: NDArray[np.floating],
    heights: NDArray[np.floating],
    vertices: NDArray[np.floating],
    *,
    tol: float = 1e-9,
) -> tuple[list[list[int]], list[tuple[int, int]], list[list[int]]]:
    """Extract face structure from polytope vertices.

    Args:
        normals: Facet normals, shape (n_facets, 4)
        heights: Facet heights
        vertices: Vertex coordinates
        tol: Tolerance

    Returns:
        Tuple of (facet_vertices, edges, faces_2d)
    """
    n_facets = normals.shape[0]

    # Find vertices on each facet
    facet_vertices = []
    for i in range(n_facets):
        verts_on_facet = _vertices_on_facet(vertices, normals[i], heights[i], tol)
        facet_vertices.append(verts_on_facet)

    # Find 2-faces (intersections of pairs of facets)
    faces_2d = []
    for i, j in combinations(range(n_facets), 2):
        common = set(facet_vertices[i]) & set(facet_vertices[j])
        if len(common) >= 3:
            faces_2d.append(list(common))

    # Find edges (1-faces)
    edges: list[tuple[int, int]] = []
    n_vertices = len(vertices)

    for i, j in combinations(range(n_vertices), 2):
        shared_facets = sum(1 for fv in facet_vertices if i in fv and j in fv)
        if shared_facets >= 3:
            edges.append((i, j))

    return facet_vertices, edges, faces_2d


def build_polytope_geometry(
    normals: Sequence[Sequence[float]] | NDArray[np.floating],
    heights: Sequence[float] | NDArray[np.floating],
    *,
    tol: float = 1e-9,
) -> PolytopeGeometry:
    """Build complete polytope geometry from H-representation.

    Args:
        normals: Facet normal vectors
        heights: Facet heights
        tol: Numerical tolerance

    Returns:
        PolytopeGeometry with all face structure computed
    """
    normals_arr = np.asarray(normals, dtype=np.float64)
    heights_arr = np.asarray(heights, dtype=np.float64)

    vertices = hrep_to_vertices(normals_arr, heights_arr, tol=tol)
    facet_vertices, edges, faces_2d = extract_faces(
        normals_arr, heights_arr, vertices, tol=tol
    )

    return PolytopeGeometry(
        normals=normals_arr,
        heights=heights_arr,
        vertices=vertices,
        facet_vertices=facet_vertices,
        edges=edges,
        faces_2d=faces_2d,
    )


def order_face_vertices(
    vertices: NDArray[np.floating],
    face_indices: list[int],
) -> list[int]:
    """Order vertices of a 2-face in cyclic order for rendering.

    Args:
        vertices: All vertex coordinates, shape (n, 4)
        face_indices: Indices of vertices forming the face

    Returns:
        Face indices reordered for cyclic traversal
    """
    if len(face_indices) < 3:
        return face_indices

    face_verts = vertices[face_indices]

    centroid = face_verts.mean(axis=0)
    centered = face_verts - centroid

    _, _, Vt = np.linalg.svd(centered)
    proj_2d = centered @ Vt[:2].T

    try:
        hull = ConvexHull(proj_2d)
        ordered_local = list(hull.vertices)
        return [face_indices[i] for i in ordered_local]
    except Exception:
        return face_indices


# =============================================================================
# Data Loading
# =============================================================================


def load_hko_polytope() -> tuple[list[list[float]], list[float], list[list[float]]]:
    """Load the HKO 2024 counterexample polytope data.

    Returns:
        Tuple of (normals, heights, orbit_breakpoints)
    """
    from viterbo.paths import get_data_dir
    data_path = get_data_dir("counterexample-hko") / "hko2024.json"

    with open(data_path) as f:
        data = json.load(f)

    normals = [facet["normal"] for facet in data["hrep"]["facets"]]
    heights = [facet["height"] for facet in data["hrep"]["facets"]]
    breakpoints = data["minimum_orbit"]["breakpoints"]

    return normals, heights, breakpoints


# =============================================================================
# Main
# =============================================================================


def main() -> None:
    """Build and verify polytope geometry for HKO counterexample."""
    print("Loading HKO 2024 counterexample...")
    normals, heights, breakpoints = load_hko_polytope()

    print("Building polytope geometry...")
    geom = build_polytope_geometry(normals, heights)

    print()
    print("=== Geometry Verification ===")
    print(f"Facets: {len(normals)} (expected: 10)")
    print(f"Vertices: {len(geom.vertices)} (expected: 25)")
    print(f"Edges: {len(geom.edges)} (expected: 50)")
    print(f"2-faces: {len(geom.faces_2d)} (expected: 35)")

    # Verify product structure
    q_coords = geom.vertices[:, :2]
    p_coords = geom.vertices[:, 2:]
    q_unique = set(tuple(np.round(q, 4)) for q in q_coords)
    p_unique = set(tuple(np.round(p, 4)) for p in p_coords)

    print()
    print(f"Unique q-projections: {len(q_unique)} (expected: 5)")
    print(f"Unique p-projections: {len(p_unique)} (expected: 5)")

    # Verify orbit
    bp_arr = np.array(breakpoints)
    orbit_closed = np.allclose(bp_arr[0], bp_arr[-1])
    print(f"Orbit closed: {orbit_closed}")

    # Save geometry to output
    from viterbo.paths import get_data_dir
    output_dir = get_data_dir("polytope-visualization-4d")
    output_dir.mkdir(parents=True, exist_ok=True)

    output_path = output_dir / "hko-geometry.json"
    output_data = {
        "vertices": geom.vertices.tolist(),
        "edges": geom.edges,
        "faces_2d": geom.faces_2d,
        "facet_vertices": geom.facet_vertices,
        "n_vertices": len(geom.vertices),
        "n_edges": len(geom.edges),
        "n_faces_2d": len(geom.faces_2d),
        "n_facets": len(geom.facet_vertices),
    }
    output_path.write_text(json.dumps(output_data, indent=2))
    print(f"\nSaved geometry to: {output_path}")


if __name__ == "__main__":
    main()
