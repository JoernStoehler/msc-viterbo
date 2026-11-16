# Billiard Algorithm Test Specification

## 2D Polygons

```rust
triangle := Polygon2D::regular(3, 1.0, 0.0)
square := Polygon2D::square(2.0)
pentagon := Polygon2D::regular(5, 1.0, 0.0)
hexagon := Polygon2D::regular(6, 1.0, 0.0)
heptagon := Polygon2D::regular(7, 1.0, 0.0)

rectangle := Polygon2D::from_vertices([(-1.0, -2.0), (1.0, -2.0), (1.0, 2.0), (-1.0, 2.0)])
rectangle2 := Polygon2D::from_vertices([(-1.5, -1.0), (1.5, -1.0), (1.5, 1.0), (-1.5, 1.0)])
needle_rect := Polygon2D::from_vertices([(-0.1, -1.0), (0.1, -1.0), (0.1, 1.0), (-0.1, 1.0)])

square_half := square.scale(0.5)
square_double := square.scale(2.0)
square_triple := square.scale(3.0)
triangle_double := triangle.scale(2.0)
triangle_1p5 := triangle.scale(1.5)

square_rot45 := square.rotate(PI/4)
pentagon_rot45 := pentagon.rotate(PI/4)
triangle_rot15 := triangle.rotate(15.0 * PI / 180.0)
triangle_rot25 := triangle.rotate(25.0 * PI / 180.0)
triangle_rot30 := triangle.rotate(30.0 * PI / 180.0)
triangle_rot60 := triangle.rotate(60.0 * PI / 180.0)
triangle_rot90 := triangle.rotate(90.0 * PI / 180.0)

triangle_1p5_rot25 := triangle.scale(1.5).rotate(25.0 * PI / 180.0)

almost_triangle := Polygon2D::from_vertices([(1.0, 0.0), (-0.5, 0.866), (-0.5, -0.866), (-0.48, 0.0)])
flat_triangle := Polygon2D::from_vertices([(2.0, 0.0), (-1.0, 0.01), (-1.0, -0.01)])
obtuse_triangle := Polygon2D::from_vertices([(2.0, 0.0), (-1.0, 0.3), (-1.0, -0.3)])
asymmetric_tri_a := Polygon2D::from_vertices([(1.0, 0.0), (-0.5, 0.866), (-0.5, -0.866)])
asymmetric_tri_b := Polygon2D::from_vertices([(0.8, 0.0), (-0.6, 0.7), (-0.4, -0.9)])
```

Polygons = {all 25 polygons defined above}

---

## Task 1: Orbit Validation Tests

Test all Lagrangian products K_q × K_p where K_q ∈ Polygons and K_p ∈ Polygons.

(This is the Cartesian product Polygons × Polygons, giving 25 × 25 = 625 products total.)

For each product, verify these properties:

**P1 Boundary containment:** All breakpoints lie on the boundary of the 4D polytope

**P2 Closure:** Sum of all displacement vectors equals zero

**P3 Positive finite capacity:** The capacity value is positive and finite

**P4 Reeb direction:** Each segment's displacement lies in the positive cone of Reeb vectors for active facets at the segment start

**P5 Scaling law:** For scaling factors 0.5, 2.0, and 3.0, verify that capacity scales quadratically

---

## Task 2: Algorithm Comparison Tests

Compare billiard algorithm against HK2017 algorithm on all Lagrangian products K_q × K_p where K_q ∈ Polygons and K_p ∈ Polygons.

(This is the Cartesian product Polygons × Polygons, giving 25 × 25 = 625 products total.)

For each product: compute capacity using both algorithms, print a table row showing the product name, billiard capacity, HK2017 capacity, and their ratio.

No assertions - just observe and document the ratios.
