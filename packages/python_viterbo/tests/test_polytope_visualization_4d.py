"""Tests for 4D polytope visualization experiment."""

from __future__ import annotations

import numpy as np
import pytest

from viterbo.experiments.polytope_visualization_4d.stage_build import (
    PolytopeGeometry,
    build_polytope_geometry,
    extract_faces,
    hrep_to_vertices,
    interpolate_4d_segment,
    order_face_vertices,
    project_4d_points,
    project_4d_segment_to_3d,
    project_4d_to_3d,
    radial_project_to_s3,
    stereographic_s3_to_r3,
)


class TestRadialProjection:
    """Tests for radial projection to S³."""

    def test_unit_vector_unchanged(self) -> None:
        """Unit vectors should project to themselves."""
        v = np.array([1.0, 0.0, 0.0, 0.0])
        result = radial_project_to_s3(v)
        np.testing.assert_allclose(result, v)

    def test_scales_to_unit_norm(self) -> None:
        """Any non-zero vector should project to unit norm."""
        v = np.array([3.0, 4.0, 0.0, 0.0])
        result = radial_project_to_s3(v)
        assert abs(np.linalg.norm(result) - 1.0) < 1e-10

    def test_preserves_direction(self) -> None:
        """Projection should preserve direction."""
        v = np.array([1.0, 2.0, 3.0, 4.0])
        result = radial_project_to_s3(v)
        # Check that result is a positive scalar multiple of v
        scale = np.linalg.norm(v)
        np.testing.assert_allclose(result, v / scale)

    def test_raises_on_zero_vector(self) -> None:
        """Should raise ValueError for zero vector."""
        v = np.array([0.0, 0.0, 0.0, 0.0])
        with pytest.raises(ValueError, match="too close to origin"):
            radial_project_to_s3(v)


class TestStereographicProjection:
    """Tests for stereographic projection S³ → R³."""

    def test_equator_point(self) -> None:
        """Points on equator (w=0) project straightforwardly."""
        v = np.array([1.0, 0.0, 0.0, 0.0])  # On equator
        result = stereographic_s3_to_r3(v)
        np.testing.assert_allclose(result, [1.0, 0.0, 0.0])

    def test_antipodal_to_pole(self) -> None:
        """Point opposite to pole projects to origin."""
        v = np.array([0.0, 0.0, 0.0, -1.0])  # Antipodal to (0,0,0,1)
        result = stereographic_s3_to_r3(v)
        np.testing.assert_allclose(result, [0.0, 0.0, 0.0])

    def test_halfway_point(self) -> None:
        """Point halfway between equator and pole."""
        # Point at w = 0.5, on unit sphere: need (x,y,z) with x²+y²+z² = 1 - 0.25 = 0.75
        w = 0.5
        x = np.sqrt(0.75)
        v = np.array([x, 0.0, 0.0, w])
        result = stereographic_s3_to_r3(v)
        # x / (1 - w) = sqrt(0.75) / 0.5 = sqrt(0.75) * 2
        expected_x = x / (1 - w)
        np.testing.assert_allclose(result, [expected_x, 0.0, 0.0])


class TestCombinedProjection:
    """Tests for the combined 4D → 3D projection pipeline."""

    def test_simple_point(self) -> None:
        """Test projection of a simple 4D point."""
        v = np.array([1.0, 1.0, 1.0, 0.0])
        result = project_4d_to_3d(v)
        # Should be 3D vector
        assert result.shape == (3,)

    def test_multiple_points(self) -> None:
        """Test batch projection of multiple points."""
        points = np.array([
            [1.0, 0.0, 0.0, 0.0],
            [0.0, 1.0, 0.0, 0.0],
            [0.0, 0.0, 1.0, 0.0],
            [1.0, 1.0, 1.0, 0.0],
        ])
        result = project_4d_points(points)
        assert result.shape == (4, 3)


class TestSegmentInterpolation:
    """Tests for 4D segment interpolation and projection."""

    def test_interpolation_endpoints(self) -> None:
        """Interpolation should include exact endpoints."""
        start = np.array([1.0, 0.0, 0.0, 0.0])
        end = np.array([0.0, 1.0, 0.0, 0.0])
        result = interpolate_4d_segment(start, end, n_samples=5)

        np.testing.assert_allclose(result[0], start)
        np.testing.assert_allclose(result[-1], end)

    def test_interpolation_count(self) -> None:
        """Interpolation should produce correct number of samples."""
        start = np.array([1.0, 0.0, 0.0, 0.0])
        end = np.array([0.0, 1.0, 0.0, 0.0])
        result = interpolate_4d_segment(start, end, n_samples=10)
        assert result.shape == (10, 4)

    def test_segment_projection_shape(self) -> None:
        """Projected segment should have correct shape."""
        start = np.array([1.0, 0.0, 0.0, 0.0])
        end = np.array([0.0, 1.0, 0.0, 0.0])
        result = project_4d_segment_to_3d(start, end, n_samples=15)
        assert result.shape == (15, 3)


class TestHrepToVertices:
    """Tests for H-representation to V-representation conversion."""

    def test_simplex(self) -> None:
        """Test vertex enumeration for a 4D simplex."""
        # Regular 4-simplex with vertices at coordinate axes + origin
        # The simplex conv(0, e1, e2, e3, e4) has 5 facets
        # But we need origin in interior, so use a different simplex

        # Simplex with vertices at (±1, 0, 0, 0), (0, ±1, 0, 0), etc.
        # shifted to have origin inside
        # For simplicity, use the cross-polytope (orthoplex)

        # Cross-polytope: conv(±e1, ±e2, ±e3, ±e4)
        # H-rep: 16 facets with normals (±1, ±1, ±1, ±1)/2 and height 1
        normals = []
        for s1 in [-1, 1]:
            for s2 in [-1, 1]:
                for s3 in [-1, 1]:
                    for s4 in [-1, 1]:
                        normals.append([s1, s2, s3, s4])
        normals = np.array(normals, dtype=np.float64) / 2  # Normalize
        heights = np.ones(16)

        vertices = hrep_to_vertices(normals, heights)

        # Cross-polytope has 8 vertices: ±e1, ±e2, ±e3, ±e4
        assert vertices.shape[0] == 8

    def test_cube(self) -> None:
        """Test vertex enumeration for a 4D hypercube."""
        # 4D cube [-1, 1]^4 has 8 facets (2 per axis)
        normals = np.array([
            [1, 0, 0, 0],
            [-1, 0, 0, 0],
            [0, 1, 0, 0],
            [0, -1, 0, 0],
            [0, 0, 1, 0],
            [0, 0, -1, 0],
            [0, 0, 0, 1],
            [0, 0, 0, -1],
        ], dtype=np.float64)
        heights = np.ones(8)

        vertices = hrep_to_vertices(normals, heights)

        # 4D cube has 2^4 = 16 vertices
        assert vertices.shape[0] == 16

        # All vertices should be at corners (±1, ±1, ±1, ±1)
        for v in vertices:
            assert all(abs(abs(c) - 1) < 1e-9 for c in v)


class TestFaceExtraction:
    """Tests for polytope face extraction."""

    def test_cube_faces(self) -> None:
        """Test face extraction for a 4D hypercube."""
        # 4D cube
        normals = np.array([
            [1, 0, 0, 0],
            [-1, 0, 0, 0],
            [0, 1, 0, 0],
            [0, -1, 0, 0],
            [0, 0, 1, 0],
            [0, 0, -1, 0],
            [0, 0, 0, 1],
            [0, 0, 0, -1],
        ], dtype=np.float64)
        heights = np.ones(8)

        vertices = hrep_to_vertices(normals, heights)
        facet_vertices, edges, faces_2d = extract_faces(normals, heights, vertices)

        # Each facet (3-face) should have 8 vertices (a 3D cube)
        assert len(facet_vertices) == 8
        for fv in facet_vertices:
            assert len(fv) == 8

        # 4D cube has 32 edges
        assert len(edges) == 32

        # 4D cube has 24 2-faces (squares)
        assert len(faces_2d) == 24


class TestBuildPolytopeGeometry:
    """Tests for the complete geometry building pipeline."""

    def test_builds_from_lists(self) -> None:
        """Test building geometry from Python lists."""
        # Simple cube
        normals = [
            [1, 0, 0, 0],
            [-1, 0, 0, 0],
            [0, 1, 0, 0],
            [0, -1, 0, 0],
            [0, 0, 1, 0],
            [0, 0, -1, 0],
            [0, 0, 0, 1],
            [0, 0, 0, -1],
        ]
        heights = [1.0] * 8

        geom = build_polytope_geometry(normals, heights)

        assert geom.vertices.shape[0] == 16
        assert len(geom.edges) == 32
        assert len(geom.faces_2d) == 24


class TestOrderFaceVertices:
    """Tests for cyclic ordering of face vertices."""

    def test_square_ordering(self) -> None:
        """Test ordering vertices of a square face."""
        # Square in a plane
        vertices = np.array([
            [0, 0, 0, 0],
            [1, 0, 0, 0],
            [1, 1, 0, 0],
            [0, 1, 0, 0],
        ], dtype=np.float64)
        face_indices = [0, 1, 2, 3]

        ordered = order_face_vertices(vertices, face_indices)

        # Should return all 4 vertices in some cyclic order
        assert len(ordered) == 4
        assert set(ordered) == {0, 1, 2, 3}
