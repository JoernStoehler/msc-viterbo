# polytope-visualization-4d Experiment

**Status:** Complete

## Research Question

How can we visualize 4D polytopes and Reeb dynamics in 3D (rendered to 2D screen)?

## Method

Projection pipeline:
1. **Radial projection to S³:** For polytope K star-shaped w.r.t. 0, map v ∈ ∂K to v/|v| ∈ S³
2. **Stereographic projection S³ → R³:** Standard conformal map (preserves angles, curves straight edges)
3. **3D rendering:** Plotly for interactive visualization

What to render:

*Polytope structure:*
- 3-facets become volumes with piecewise-smooth boundary
- 2-faces → translucent curved surfaces (triangulated mesh)
- 1-faces → curved lines (edges)
- 0-faces → points (vertices)

*Reeb dynamics:*
- Reeb trajectories → curved/piecewise-smooth lines with direction arrows
- Breakpoints → diamond markers

## Success Criteria

1. Correct geometry extraction from H-rep (vertex count, edge count, face count match expected values)
2. Projection math produces valid 3D coordinates
3. HKO 2024 counterexample renders correctly:
   - 10 facets, 25 vertices, 50 edges, 35 2-faces
   - Pentagon × Pentagon product structure visible
   - Closed Reeb orbit visible

## Expected Outputs

- `data/polytope-visualization-4d/hko-polytope.html` - Interactive visualization
- `data/polytope-visualization-4d/hko-polytope.json` - Plotly spec for embedding
