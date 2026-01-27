"""Polytope geometry utilities for 4D visualization.

Provides H-rep to V-rep conversion and face extraction for 4D polytopes.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from typing import Sequence

import numpy as np
from numpy.typing import NDArray
from scipy.optimize import linprog
from scipy.spatial import ConvexHull


@dataclass
class PolytopeGeometry:
    """Complete geometric description of a 4D polytope.

    Contains both H-representation and extracted V-representation with
    face structure.

    Attributes:
        normals: Facet normal vectors, shape (n_facets, 4)
        heights: Facet heights, shape (n_facets,)
        vertices: Vertex coordinates, shape (n_vertices, 4)
        facet_vertices: List of vertex indices for each facet (3-face)
        edges: List of (i, j) vertex index pairs for 1-faces
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
    interior_point: NDArray[np.floating] | None = None,
    tol: float = 1e-9,
) -> NDArray[np.floating]:
    """Convert H-representation to V-representation (vertices).

    The polytope is defined as K = {x : n_i · x <= h_i} for all i.

    Uses a vertex enumeration approach: finds all vertices by checking
    which 4-combinations of hyperplanes intersect at a feasible point.

    Args:
        normals: Facet normal vectors, shape (n_facets, 4)
        heights: Facet heights, shape (n_facets,)
        interior_point: A point known to be in the polytope interior
                       (default: origin, assuming polytope is star-shaped)
        tol: Tolerance for feasibility checking

    Returns:
        Vertex coordinates, shape (n_vertices, 4)
    """
    n_facets = normals.shape[0]

    if interior_point is None:
        interior_point = np.zeros(4)

    vertices = []

    # In 4D, vertices are intersections of exactly 4 hyperplanes
    for facet_indices in combinations(range(n_facets), 4):
        # Build system of 4 equations: n_i · x = h_i
        A = normals[list(facet_indices)]
        b = heights[list(facet_indices)]

        # Check if system has unique solution
        try:
            x = np.linalg.solve(A, b)
        except np.linalg.LinAlgError:
            # Singular system - hyperplanes don't meet at a point
            continue

        # Check if solution is feasible (satisfies all constraints)
        if np.all(normals @ x <= heights + tol):
            # Check if this vertex is new (not a duplicate)
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
    """Find a strictly interior point of the polytope using LP.

    Solves: max s such that n_i · x <= h_i - s for all i
    """
    n_facets = normals.shape[0]

    # Variables: [x_0, x_1, x_2, x_3, s]
    # Minimize -s (= maximize s)
    c = np.zeros(5)
    c[4] = -1  # Minimize -s

    # Constraints: n_i · x + s <= h_i
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

    Computes:
    - 3-faces (facets): which vertices belong to each facet
    - 2-faces: intersections of pairs of facets
    - 1-faces (edges): intersections of sets of 3 facets

    Args:
        normals: Facet normals, shape (n_facets, 4)
        heights: Facet heights
        vertices: Vertex coordinates
        tol: Tolerance for incidence testing

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
        if len(common) >= 3:  # A 2-face in 4D needs at least 3 vertices
            faces_2d.append(list(common))

    # Find edges (1-faces)
    # An edge exists between vertices if they share at least 3 facets
    edges: list[tuple[int, int]] = []
    n_vertices = len(vertices)

    for i, j in combinations(range(n_vertices), 2):
        # Count shared facets
        shared_facets = sum(
            1
            for fv in facet_vertices
            if i in fv and j in fv
        )
        if shared_facets >= 3:  # In 4D, edge is intersection of 3 hyperplanes
            edges.append((i, j))

    return facet_vertices, edges, faces_2d


def build_polytope_geometry(
    normals: Sequence[Sequence[float]] | NDArray[np.floating],
    heights: Sequence[float] | NDArray[np.floating],
    *,
    tol: float = 1e-9,
) -> PolytopeGeometry:
    """Build complete polytope geometry from H-representation.

    This is the main entry point for polytope visualization.

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

    Uses the convex hull in the 2D subspace of the face.

    Args:
        vertices: All vertex coordinates, shape (n, 4)
        face_indices: Indices of vertices forming the face

    Returns:
        Face indices reordered for cyclic traversal
    """
    if len(face_indices) < 3:
        return face_indices

    face_verts = vertices[face_indices]

    # Project to 2D by finding the principal axes
    centroid = face_verts.mean(axis=0)
    centered = face_verts - centroid

    # SVD to get 2D subspace
    _, _, Vt = np.linalg.svd(centered)

    # Project onto first 2 principal components
    proj_2d = centered @ Vt[:2].T

    # Use convex hull to order
    try:
        hull = ConvexHull(proj_2d)
        ordered_local = list(hull.vertices)
        return [face_indices[i] for i in ordered_local]
    except Exception:
        # Fall back to original order if hull fails
        return face_indices
