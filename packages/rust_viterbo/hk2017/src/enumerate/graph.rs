//! Graph-based permutation enumeration.
//!
//! Builds a facet transition graph where edge i -> j exists if the Reeb flow
//! from facet i can reach facet j. Then enumerates only cycles in this graph,
//! which represent valid closed orbits.
//!
//! This can be much faster than naive enumeration for polytopes where the
//! transition graph is sparse.

use super::{Permutation, PermutationEnumerator};
use crate::types::FacetData;

/// Graph-based enumerator that only considers valid transition cycles.
pub struct GraphEnumerator;

impl PermutationEnumerator for GraphEnumerator {
    fn enumerate(&self, facet_data: &FacetData) -> Vec<Permutation> {
        let graph = build_transition_graph(facet_data);
        enumerate_cycles(&graph, facet_data.num_facets)
    }

    fn name(&self) -> &'static str {
        "graph-pruned"
    }
}

/// Adjacency list representation of the transition graph.
///
/// `adjacency[i]` contains the list of facets j such that Reeb flow from
/// facet i can reach facet j.
pub type TransitionGraph = Vec<Vec<usize>>;

/// Build the facet transition graph.
///
/// Edge i -> j exists if the Reeb flow from facet i (direction p_i) can
/// reach facet j. This requires:
/// - <p_i, n_j> > 0 (flow is approaching j from inside)
///
/// Note: This is a necessary but not sufficient condition. The flow might
/// hit another facet first. However, this gives a valid superset of reachable
/// facets, so the cycle enumeration is still correct (it may include some
/// infeasible cycles, but those will be rejected during QP solving).
pub fn build_transition_graph(facet_data: &FacetData) -> TransitionGraph {
    let f = facet_data.num_facets;
    let mut adjacency: TransitionGraph = vec![Vec::new(); f];

    for i in 0..f {
        let p_i = &facet_data.reeb_vectors[i];

        for j in 0..f {
            if i == j {
                continue;
            }

            // Flow from facet i goes in direction p_i.
            // It can reach facet j if <p_i, n_j> > 0 (approaching from inside).
            let dot = p_i.dot(&facet_data.normals[j]);
            if dot > 1e-10 {
                adjacency[i].push(j);
            }
        }
    }

    adjacency
}

/// Enumerate all simple cycles in the transition graph.
///
/// A cycle is a sequence [i0, i1, ..., ik-1] where:
/// - Each i_m -> i_{m+1} is an edge in the graph
/// - i_{k-1} -> i_0 is an edge (cycle closes)
/// - All vertices are distinct (simple cycle)
pub fn enumerate_cycles(graph: &TransitionGraph, max_length: usize) -> Vec<Permutation> {
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
    graph: &TransitionGraph,
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
    use nalgebra::Vector4;
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
    fn test_transition_graph_structure() {
        let polytope = make_tesseract();
        let facet_data = FacetData::from_polytope(&polytope).unwrap();
        let graph = build_transition_graph(&facet_data);

        // Should have 8 vertices
        assert_eq!(graph.len(), 8);

        // Normals and Reeb vectors for tesseract:
        // n_0 = (1,0,0,0), p_0 = 2*J*n_0 = 2*(-0,-0,1,0) = (0,0,2,0)
        // n_1 = (-1,0,0,0), p_1 = 2*(0,0,-1,0) = (0,0,-2,0)
        // n_2 = (0,1,0,0), p_2 = 2*(0,0,0,1) = (0,0,0,2)
        // n_3 = (0,-1,0,0), p_3 = (0,0,0,-2)
        // n_4 = (0,0,1,0), p_4 = 2*(-1,0,0,0) = (-2,0,0,0)
        // n_5 = (0,0,-1,0), p_5 = (2,0,0,0)
        // n_6 = (0,0,0,1), p_6 = (0,-2,0,0)
        // n_7 = (0,0,0,-1), p_7 = (0,2,0,0)

        // From facet 0 (p_0 = (0,0,2,0)):
        // <p_0, n_4> = 2 > 0, so 0 -> 4
        // <p_0, n_5> = -2 < 0, so no edge 0 -> 5
        assert!(graph[0].contains(&4));
        assert!(!graph[0].contains(&5));
    }

    #[test]
    fn test_cycles_are_valid() {
        let polytope = make_tesseract();
        let facet_data = FacetData::from_polytope(&polytope).unwrap();
        let graph = build_transition_graph(&facet_data);
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

            // Check edges exist
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
        let graph = build_transition_graph(&facet_data);
        let cycles = enumerate_cycles(&graph, facet_data.num_facets);

        // Graph pruning should reduce the number of permutations
        // (this is a basic sanity check, not a guarantee for all polytopes)
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
        let graph = build_transition_graph(&facet_data);
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
