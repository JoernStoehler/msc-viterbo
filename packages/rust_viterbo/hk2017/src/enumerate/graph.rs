//! Graph-based permutation enumeration.
//!
//! Builds a facet adjacency graph where edge i -- j exists if facets i and j
//! share at least one vertex (geometric adjacency). Then enumerates only cycles
//! in this graph, pruning permutations that cannot correspond to valid orbits.
//!
//! This can be much faster than naive enumeration for polytopes where the
//! adjacency graph is sparse.

use itertools::Itertools;
use nalgebra::{Matrix4, Vector4};

use super::{Permutation, PermutationEnumerator};
use crate::types::FacetData;

/// Graph-based enumerator that only considers cycles through adjacent facets.
pub struct GraphEnumerator;

impl PermutationEnumerator for GraphEnumerator {
    fn enumerate(&self, facet_data: &FacetData) -> Vec<Permutation> {
        let graph = build_adjacency_graph(facet_data);
        enumerate_cycles(&graph, facet_data.num_facets)
    }

    fn name(&self) -> &'static str {
        "graph-pruned"
    }
}

/// Adjacency list representation of the facet adjacency graph.
///
/// `adjacency[i]` contains the list of facets j such that facets i and j
/// share at least one vertex.
pub type AdjacencyGraph = Vec<Vec<usize>>;

/// Build the facet adjacency graph based on shared vertices.
///
/// Two facets are adjacent (share a vertex) if there exists a point x such that:
/// - n_i · x = h_i (on facet i)
/// - n_j · x = h_j (on facet j)
/// - n_k · x ≤ h_k for all other k (inside the polytope)
///
/// For polytopes in R^4 with a small number of facets, we compute this by:
/// 1. Enumerating all vertices (intersections of 4 hyperplanes)
/// 2. Building facet-vertex incidence
/// 3. Two facets are adjacent iff they share at least one vertex
pub fn build_adjacency_graph(facet_data: &FacetData) -> AdjacencyGraph {
    let f = facet_data.num_facets;

    // Enumerate vertices and their incident facets
    let (vertices, incidence) = enumerate_vertices(facet_data);

    // Build adjacency: facets i and j are adjacent if they share a vertex
    let mut adjacency: AdjacencyGraph = vec![Vec::new(); f];

    for vertex_facets in &incidence {
        // For each pair of facets incident to this vertex, they are adjacent
        for i in 0..vertex_facets.len() {
            for j in (i + 1)..vertex_facets.len() {
                let fi = vertex_facets[i];
                let fj = vertex_facets[j];

                // Add both directions (undirected graph, but we store directed)
                if !adjacency[fi].contains(&fj) {
                    adjacency[fi].push(fj);
                }
                if !adjacency[fj].contains(&fi) {
                    adjacency[fj].push(fi);
                }
            }
        }
    }

    // Debug assertion: verify adjacency is symmetric and non-reflexive
    debug_assert!(verify_adjacency_graph(
        &adjacency, &vertices, &incidence, facet_data
    ));

    adjacency
}

/// Enumerate all vertices of the polytope and their incident facets.
///
/// A vertex is the intersection of exactly 4 hyperplanes (in R^4) that lies
/// inside all other half-spaces.
///
/// Returns: (vertices, incidence) where incidence[v] is the list of facet
/// indices that vertex v lies on.
fn enumerate_vertices(facet_data: &FacetData) -> (Vec<Vector4<f64>>, Vec<Vec<usize>>) {
    let f = facet_data.num_facets;
    let mut vertices = Vec::new();
    let mut incidence = Vec::new();

    const TOLERANCE: f64 = 1e-10;

    // Try all combinations of 4 facets
    for combo in (0..f).combinations(4) {
        // Build the 4x4 system: A * x = b where A[i] = n_{combo[i]}, b[i] = h_{combo[i]}
        let mut a = Matrix4::zeros();
        let mut b = Vector4::zeros();

        for (row, &facet_idx) in combo.iter().enumerate() {
            let n = &facet_data.normals[facet_idx];
            a.set_row(row, &n.transpose());
            b[row] = facet_data.heights[facet_idx];
        }

        // Solve the linear system
        let lu = a.lu();
        if let Some(x) = lu.solve(&b) {
            // Check if this point satisfies all other half-space constraints
            let mut is_vertex = true;
            let mut incident_facets: Vec<usize> = combo.clone();

            for k in 0..f {
                let slack = facet_data.heights[k] - facet_data.normals[k].dot(&x);

                if slack < -TOLERANCE {
                    // Point is outside this half-space, not a valid vertex
                    is_vertex = false;
                    break;
                }

                // If slack is essentially zero, this facet is also incident
                if slack.abs() < TOLERANCE && !incident_facets.contains(&k) {
                    incident_facets.push(k);
                }
            }

            if is_vertex {
                // Check for duplicate vertices (can happen with degenerate polytopes)
                let is_duplicate = vertices
                    .iter()
                    .any(|v: &Vector4<f64>| (v - x).norm() < TOLERANCE);

                if !is_duplicate {
                    incident_facets.sort();
                    vertices.push(x);
                    incidence.push(incident_facets);
                }
            }
        }
        // If system is singular, these 4 facets don't define a vertex
    }

    (vertices, incidence)
}

/// Verify the adjacency graph is consistent (debug only).
fn verify_adjacency_graph(
    adjacency: &AdjacencyGraph,
    _vertices: &[Vector4<f64>],
    _incidence: &[Vec<usize>],
    _facet_data: &FacetData,
) -> bool {
    let f = adjacency.len();

    // Check symmetry
    for i in 0..f {
        for &j in &adjacency[i] {
            if !adjacency[j].contains(&i) {
                eprintln!(
                    "Adjacency not symmetric: {} -> {} but not {} -> {}",
                    i, j, j, i
                );
                return false;
            }
        }
    }

    // Check no self-loops
    for i in 0..f {
        if adjacency[i].contains(&i) {
            eprintln!("Self-loop found: {} -> {}", i, i);
            return false;
        }
    }

    true
}

/// Enumerate all simple cycles in the adjacency graph.
///
/// A cycle is a sequence [i0, i1, ..., ik-1] where:
/// - Each i_m and i_{m+1} are adjacent (share a vertex)
/// - i_{k-1} and i_0 are adjacent (cycle closes)
/// - All facets are distinct (simple cycle)
pub fn enumerate_cycles(graph: &AdjacencyGraph, max_length: usize) -> Vec<Permutation> {
    let f = graph.len();
    let mut cycles = Vec::new();

    // DFS from each starting vertex
    for start in 0..f {
        let mut path = vec![start];
        let mut visited = vec![false; f];
        visited[start] = true;
        dfs_cycles(
            start,
            &mut path,
            &mut visited,
            graph,
            max_length,
            &mut cycles,
        );
    }

    // Remove duplicate cycles (same cycle starting at different points)
    deduplicate_cycles(&mut cycles);

    cycles
}

/// DFS to find all cycles starting and ending at `start`.
fn dfs_cycles(
    start: usize,
    path: &mut Vec<usize>,
    visited: &mut [bool],
    graph: &AdjacencyGraph,
    max_length: usize,
    cycles: &mut Vec<Permutation>,
) {
    if path.len() > max_length {
        return;
    }

    let current = *path.last().unwrap();

    for &next in &graph[current] {
        if next == start && path.len() >= 2 {
            // Found a cycle back to start
            cycles.push(path.clone());
        } else if !visited[next] {
            // Continue exploring
            visited[next] = true;
            path.push(next);
            dfs_cycles(start, path, visited, graph, max_length, cycles);
            path.pop();
            visited[next] = false;
        }
    }
}

/// Remove duplicate cycles.
///
/// Two cycles are considered the same if one is a rotation of the other.
/// We canonicalize by rotating to start at the minimum element.
fn deduplicate_cycles(cycles: &mut Vec<Permutation>) {
    // Canonicalize each cycle
    for cycle in cycles.iter_mut() {
        *cycle = canonicalize_cycle(cycle);
    }

    // Sort and deduplicate
    cycles.sort();
    cycles.dedup();
}

/// Canonicalize a cycle by rotating it to start at the minimum element.
fn canonicalize_cycle(cycle: &[usize]) -> Permutation {
    if cycle.is_empty() {
        return Vec::new();
    }

    // Find position of minimum element
    let min_pos = cycle
        .iter()
        .enumerate()
        .min_by_key(|&(_, &v)| v)
        .map(|(i, _)| i)
        .unwrap();

    // Rotate to start at minimum
    let mut canonical = Vec::with_capacity(cycle.len());
    for i in 0..cycle.len() {
        canonical.push(cycle[(min_pos + i) % cycle.len()]);
    }
    canonical
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::PolytopeHRep;

    fn make_tesseract() -> PolytopeHRep {
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, -1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, -1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0),
            Vector4::new(0.0, 0.0, 0.0, -1.0),
        ];
        let heights = vec![1.0; 8];
        PolytopeHRep::new(normals, heights)
    }

    #[test]
    fn test_canonicalize_cycle() {
        assert_eq!(canonicalize_cycle(&[2, 0, 1]), vec![0, 1, 2]);
        assert_eq!(canonicalize_cycle(&[3, 1, 2]), vec![1, 2, 3]);
        assert_eq!(canonicalize_cycle(&[0, 1, 2]), vec![0, 1, 2]);
    }

    #[test]
    fn test_vertex_enumeration_tesseract() {
        let polytope = make_tesseract();
        let facet_data = FacetData::from_polytope(&polytope).unwrap();

        let (vertices, incidence) = enumerate_vertices(&facet_data);

        // Tesseract [-1,1]^4 has 2^4 = 16 vertices
        assert_eq!(vertices.len(), 16, "Tesseract should have 16 vertices");

        // Each vertex is incident to exactly 4 facets (one per coordinate direction)
        for (i, facets) in incidence.iter().enumerate() {
            assert_eq!(
                facets.len(),
                4,
                "Vertex {} should be incident to 4 facets, got {:?}",
                i,
                facets
            );
        }
    }

    #[test]
    fn test_adjacency_graph_tesseract() {
        let polytope = make_tesseract();
        let facet_data = FacetData::from_polytope(&polytope).unwrap();
        let graph = build_adjacency_graph(&facet_data);

        // Should have 8 facets
        assert_eq!(graph.len(), 8);

        // For the tesseract, facets i and j are adjacent iff their normals are orthogonal.
        // Opposite facets (0,1), (2,3), (4,5), (6,7) have parallel normals -> NOT adjacent.
        // All other pairs have orthogonal normals -> adjacent.
        assert!(
            !graph[0].contains(&1),
            "Opposite facets 0,1 should not be adjacent"
        );
        assert!(
            !graph[2].contains(&3),
            "Opposite facets 2,3 should not be adjacent"
        );
        assert!(
            !graph[4].contains(&5),
            "Opposite facets 4,5 should not be adjacent"
        );
        assert!(
            !graph[6].contains(&7),
            "Opposite facets 6,7 should not be adjacent"
        );

        // Non-opposite pairs should be adjacent
        assert!(graph[0].contains(&2), "Facets 0,2 should be adjacent");
        assert!(graph[0].contains(&4), "Facets 0,4 should be adjacent");
        assert!(graph[0].contains(&6), "Facets 0,6 should be adjacent");

        // Each facet should have exactly 6 neighbors (all except itself and its opposite)
        for i in 0..8 {
            assert_eq!(
                graph[i].len(),
                6,
                "Facet {} should have 6 neighbors, got {}",
                i,
                graph[i].len()
            );
        }
    }

    #[test]
    fn test_optimal_permutation_is_valid_cycle() {
        // The optimal permutation [0, 2, 5, 1, 4, 6] should be a valid cycle
        // in the adjacency graph (all consecutive pairs are adjacent).
        let polytope = make_tesseract();
        let facet_data = FacetData::from_polytope(&polytope).unwrap();
        let graph = build_adjacency_graph(&facet_data);

        let optimal = vec![0, 2, 5, 1, 4, 6];

        for i in 0..optimal.len() {
            let from = optimal[i];
            let to = optimal[(i + 1) % optimal.len()];
            assert!(
                graph[from].contains(&to),
                "Optimal permutation edge {} -> {} should exist in adjacency graph",
                from,
                to
            );
        }
    }

    #[test]
    fn test_cycles_are_valid() {
        let polytope = make_tesseract();
        let facet_data = FacetData::from_polytope(&polytope).unwrap();
        let graph = build_adjacency_graph(&facet_data);
        let cycles = enumerate_cycles(&graph, facet_data.num_facets);

        // Every cycle should:
        // 1. Have length >= 2
        // 2. Have all distinct elements
        // 3. Have valid edges in the graph

        for cycle in &cycles {
            assert!(cycle.len() >= 2, "Cycle too short: {:?}", cycle);

            // Check all distinct
            let mut seen = std::collections::HashSet::new();
            for &v in cycle {
                assert!(seen.insert(v), "Duplicate vertex in cycle: {:?}", cycle);
            }

            // Check edges exist (adjacency)
            for i in 0..cycle.len() {
                let from = cycle[i];
                let to = cycle[(i + 1) % cycle.len()];
                assert!(
                    graph[from].contains(&to),
                    "Invalid edge {} -> {} in cycle {:?}",
                    from,
                    to,
                    cycle
                );
            }
        }
    }

    #[test]
    fn test_graph_pruning_reduces_permutations() {
        let polytope = make_tesseract();
        let facet_data = FacetData::from_polytope(&polytope).unwrap();

        let naive_count = super::super::count_naive_permutations(8);
        let graph = build_adjacency_graph(&facet_data);
        let cycles = enumerate_cycles(&graph, facet_data.num_facets);

        // Graph pruning should reduce the number of permutations
        println!("Naive: {}, Graph-pruned: {}", naive_count, cycles.len());
        assert!(
            cycles.len() <= naive_count,
            "Graph pruning should not increase permutation count"
        );
    }

    #[test]
    fn test_no_duplicate_cycles() {
        let polytope = make_tesseract();
        let facet_data = FacetData::from_polytope(&polytope).unwrap();
        let graph = build_adjacency_graph(&facet_data);
        let cycles = enumerate_cycles(&graph, facet_data.num_facets);

        // Check no duplicates after canonicalization
        let mut seen = std::collections::HashSet::new();
        for cycle in &cycles {
            let canonical = canonicalize_cycle(cycle);
            assert!(
                seen.insert(canonical.clone()),
                "Duplicate cycle found: {:?}",
                canonical
            );
        }
    }
}
