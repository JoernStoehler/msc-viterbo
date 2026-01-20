//! Main capacity computation and algorithm trait abstraction.
//!
//! This module contains:
//! - `compute_capacity`: The branch-and-bound algorithm implementation
//! - `CapacityAlgorithm`: Trait for comparing different algorithms
//! - Algorithm implementations: TubeAlgorithm, HK2019Algorithm, MinkowskiBilliardAlgorithm
//!
//! # Mathematical references
//!
//! - **CH2021**: Chaidez-Hutchings, "Computing Reeb dynamics on polytopes",
//!   arXiv:2108.01668. Primary source for the tube algorithm.
//! - **HK2019**: Haim-Kislev, "On the symplectic capacities of convex bodies",
//!   arXiv:1907.02073. Source for the QP formulation.
//! - **Rudolf2022**: Rudolf, "Optimal bounds for Minkowski billiard complexity".

use crate::polytope::{PolytopeData, EPS_DEDUP, EPS_FEAS, EPS_LAGR};
use crate::result::{AlgorithmError, CapacityResult, Diagnostics};
use crate::tube::{get_extensions, solve_closed_tube, ExtensionResult, Tube};
use rust_viterbo_geom::{detect_near_lagrangian, perturb_polytope_normals, PolytopeHRep};
use std::collections::BinaryHeap;

/// Tolerance for rotation pruning (in turns).
const EPS_ROT: f64 = 0.01;

/// Default maximum rotation before pruning (in turns).
///
/// **Citation**: CH2021 Proposition 1.10(b) states that an action-minimizing Reeb orbit
/// has rotation ρ ≤ 2. If nondegenerate, the inequality is strict.
pub const DEFAULT_MAX_ROTATION: f64 = 2.0;

/// Configuration options for the tube algorithm.
#[derive(Clone, Debug)]
pub struct TubeAlgorithmConfig {
    /// Maximum rotation before pruning (in turns). Default: 2.0 per CH2021.
    pub max_rotation: f64,
    /// Whether to use rotation-based pruning. Default: true.
    pub use_rotation_cutoffs: bool,
    /// Whether to use action-based pruning. Default: true.
    pub use_action_bounds: bool,
}

impl Default for TubeAlgorithmConfig {
    fn default() -> Self {
        Self {
            max_rotation: DEFAULT_MAX_ROTATION,
            use_rotation_cutoffs: true,
            use_action_bounds: true,
        }
    }
}

/// Compute the EHZ capacity of a 4-dimensional convex polytope.
///
/// Uses branch-and-bound search over tube compositions.
/// See [algorithm-spec.md](../docs/algorithm-spec.md) for details.
pub fn compute_capacity(hrep: PolytopeHRep) -> Result<CapacityResult, AlgorithmError> {
    compute_capacity_with_config(hrep, TubeAlgorithmConfig::default())
}

/// Count the number of Lagrangian 2-faces (pairs where omega(n_i, n_j) = 0).
///
/// Returns (lagrangian_count, total_count) where total_count = number of 2-faces.
pub fn count_lagrangian_2faces(hrep: &PolytopeHRep) -> (usize, usize) {
    use rust_viterbo_geom::symplectic_form;

    let raw_faces = hrep.two_faces(EPS_FEAS, EPS_DEDUP);
    let total = raw_faces.len();
    let mut lagrangian_count = 0;

    for face in &raw_faces {
        let omega = symplectic_form(hrep.normals[face.i], hrep.normals[face.j]);
        if omega.abs() < EPS_LAGR {
            lagrangian_count += 1;
        }
    }

    (lagrangian_count, total)
}

/// Compute capacity with custom configuration.
///
/// This allows ablation studies by disabling rotation/action pruning
/// or adjusting the rotation cutoff.
pub fn compute_capacity_with_config(
    hrep: PolytopeHRep,
    config: TubeAlgorithmConfig,
) -> Result<CapacityResult, AlgorithmError> {
    // Step 1: Validate input
    if let Err(e) = hrep.validate(1e-6) {
        return Err(AlgorithmError::ValidationError(e.to_string()));
    }

    // Step 1b: Check for Lagrangian 2-faces BEFORE perturbation
    // The tube algorithm requires ALL 2-faces to be non-Lagrangian.
    // If any Lagrangian 2-faces exist, return InvalidInput immediately.
    let (lagrangian_count, total_2faces) = count_lagrangian_2faces(&hrep);
    if lagrangian_count > 0 {
        return Err(AlgorithmError::InvalidInput(format!(
            "polytope has {} Lagrangian 2-faces out of {}, tube algorithm requires all non-Lagrangian",
            lagrangian_count, total_2faces
        )));
    }

    // Step 2: Check for near-Lagrangian 2-faces and perturb if needed
    // Note: This is now only for numerical stability (near-zero omega values)
    let detection = detect_near_lagrangian(&hrep, EPS_LAGR, EPS_FEAS, EPS_DEDUP);

    let mut diagnostics = Diagnostics {
        best_action_found: f64::INFINITY,
        lagrangian_detection: Some(detection),
        ..Default::default()
    };

    let (hrep, perturbation) = if detection.detected {
        let seed = 42u64;
        // epsilon=1e-2 creates well-conditioned geometry with rotations
        // ~0.25 turns per 2-face. Smaller values cause numerical degeneracy
        // where the feasible polygon collapses to a line.
        let epsilon = 1e-2;
        let outcome = perturb_polytope_normals(&hrep, seed, epsilon);
        (outcome.polytope, Some(outcome.metadata))
    } else {
        (hrep, None)
    };
    diagnostics.perturbation = perturbation;

    // Step 3: Precompute polytope data
    let data = PolytopeData::new(hrep);

    // Step 4: Input validation - check for non-Lagrangian 2-faces
    // The tube algorithm CANNOT work on polytopes where ALL 2-faces are Lagrangian.
    // This is a distinct failure mode from "no orbits found" - it means the algorithm
    // is not applicable to this input.
    if data.two_faces.is_empty() {
        return Err(AlgorithmError::InvalidInput(
            "no non-Lagrangian 2-faces: tube algorithm requires at least one non-Lagrangian 2-face".to_string(),
        ));
    }

    let max_rotation = config.max_rotation;
    let use_rotation_cutoffs = config.use_rotation_cutoffs;
    let use_action_bounds = config.use_action_bounds;

    // Step 5: Initialize search
    let mut best_action = f64::INFINITY;
    let mut best_witness = None;
    let mut worklist: BinaryHeap<Tube> = BinaryHeap::new();

    // Track whether any tubes were pruned by rotation (to distinguish failure modes)
    let mut any_pruned_by_rotation = false;

    // Debug: print 2-face info
    #[cfg(test)]
    {
        eprintln!(
            "DEBUG: {} non-Lagrangian 2-faces after perturbation",
            data.two_faces.len()
        );
        for (idx, tf) in data.two_faces.iter().take(3).enumerate() {
            eprintln!(
                "  2-face[{}]: i={}, j={}, rotation={:.6}",
                idx, tf.i, tf.j, tf.rotation
            );
        }
        eprintln!(
            "DEBUG: config max_rotation={}, use_rotation_cutoffs={}, use_action_bounds={}",
            max_rotation, use_rotation_cutoffs, use_action_bounds
        );
    }

    // Create root tubes (one per non-Lagrangian 2-face)
    for two_face in &data.two_faces {
        let tube = Tube::create_root(two_face);
        if !use_rotation_cutoffs || tube.rotation <= max_rotation + EPS_ROT {
            worklist.push(tube);
        } else {
            diagnostics.nodes_pruned_rotation += 1;
            any_pruned_by_rotation = true;
        }
    }

    // Step 6: Branch-and-bound search
    #[cfg(test)]
    let mut max_seq_len = 0usize;
    #[cfg(test)]
    let mut closure_count = 0usize;

    while let Some(tube) = worklist.pop() {
        diagnostics.nodes_explored += 1;

        #[cfg(test)]
        if tube.facet_sequence.len() > max_seq_len {
            max_seq_len = tube.facet_sequence.len();
            eprintln!(
                "DEBUG: max seq_len={}, rotation={:.4}",
                max_seq_len, tube.rotation
            );
        }

        // Action pruning (if enabled)
        if use_action_bounds && tube.action_lower_bound >= best_action {
            diagnostics.nodes_pruned_action += 1;
            continue;
        }

        // Get extensions
        let extensions = get_extensions(&tube, &data);

        for ext in extensions {
            match ext {
                ExtensionResult::Extension(new_tube) => {
                    // Rotation pruning (if enabled)
                    if use_rotation_cutoffs && new_tube.rotation > max_rotation + EPS_ROT {
                        diagnostics.nodes_pruned_rotation += 1;
                        any_pruned_by_rotation = true;
                        continue;
                    }

                    // Action pruning (if enabled)
                    if use_action_bounds && new_tube.action_lower_bound >= best_action {
                        diagnostics.nodes_pruned_action += 1;
                        continue;
                    }

                    worklist.push(new_tube);
                }
                ExtensionResult::Closure(closed_tube) => {
                    #[cfg(test)]
                    {
                        closure_count += 1;
                    }
                    #[cfg(test)]
                    eprintln!(
                        "DEBUG: closure candidate #{} rotation={:.4}, seq_len={}",
                        closure_count,
                        closed_tube.rotation,
                        closed_tube.facet_sequence.len()
                    );

                    // Closure is determined geometrically by the flow map having a fixed point.
                    // **Citation**: CH2021 Definition 3.12 - periodic orbit = cycle with fixed point of φ_p.
                    //
                    // No rotation filter here. The rotation ρ ∈ (1, 2) is a CONSEQUENCE of
                    // action-minimization (CH2021 Proposition 1.10), not a PREREQUISITE for closure.
                    // The max_rotation bound already prunes orbits with ρ > max_rotation.

                    // Try to solve this closed tube
                    if let Some((action, witness)) = solve_closed_tube(&closed_tube, &data) {
                        #[cfg(test)]
                        eprintln!("DEBUG: solved closed tube, action={}", action);
                        if action < best_action && action > 0.0 {
                            best_action = action;
                            best_witness = Some(witness);
                            diagnostics.best_action_found = action;
                        }
                    }
                }
            }
        }
    }

    #[cfg(test)]
    eprintln!(
        "DEBUG: search complete. nodes={}, closures_found={}, max_seq_len={}",
        diagnostics.nodes_explored, closure_count, max_seq_len
    );

    // Return result with appropriate error type
    if best_action < f64::INFINITY {
        Ok(CapacityResult {
            capacity: best_action,
            witness: best_witness,
            diagnostics,
        })
    } else if any_pruned_by_rotation {
        // Some tubes were pruned by rotation cutoff - the search may have missed orbits
        Err(AlgorithmError::NoValidOrbits)
    } else {
        // No tubes were pruned by rotation - the search was exhaustive
        Err(AlgorithmError::SearchExhausted)
    }
}

// ============================================================================
// Algorithm Trait Abstraction
// ============================================================================

/// Metadata about an algorithm's capabilities and constraints.
#[derive(Clone, Debug)]
pub struct AlgorithmMetadata {
    pub name: &'static str,
    pub description: &'static str,
    pub requires_non_lagrangian: bool,
    pub lagrangian_product_only: bool,
    pub complexity: &'static str,
    pub max_recommended_facets: Option<usize>,
}

/// Trait for algorithms that compute symplectic capacities.
pub trait CapacityAlgorithm {
    fn metadata(&self) -> AlgorithmMetadata;
    fn supports_input(&self, hrep: &PolytopeHRep) -> Result<(), String>;
    fn compute(&self, hrep: PolytopeHRep) -> Result<CapacityResult, AlgorithmError>;

    fn timeout_hint_ms(&self, hrep: &PolytopeHRep) -> Option<u64> {
        let facets = hrep.normals.len();
        Some(1000 * facets.min(60) as u64)
    }
}

/// The tube-based branch-and-bound algorithm (CH2021).
#[derive(Clone, Debug)]
pub struct TubeAlgorithm {
    /// Whether to use rotation-based pruning. Default: true.
    pub use_rotation_cutoffs: bool,
    /// Whether to use action-based pruning. Default: true.
    pub use_action_bounds: bool,
    /// Maximum rotation before pruning (in turns). Default: 2.0 per CH2021.
    pub max_rotation: f64,
}

impl Default for TubeAlgorithm {
    fn default() -> Self {
        Self::new()
    }
}

impl TubeAlgorithm {
    pub fn new() -> Self {
        Self {
            use_rotation_cutoffs: true,
            use_action_bounds: true,
            max_rotation: DEFAULT_MAX_ROTATION,
        }
    }

    pub fn with_options(use_rotation_cutoffs: bool, use_action_bounds: bool) -> Self {
        Self {
            use_rotation_cutoffs,
            use_action_bounds,
            max_rotation: DEFAULT_MAX_ROTATION,
        }
    }

    /// Create a TubeAlgorithm with a custom rotation cutoff.
    ///
    /// This is useful for ablation studies to see if orbits exist at higher rotation.
    pub fn with_max_rotation(max_rotation: f64) -> Self {
        Self {
            use_rotation_cutoffs: true,
            use_action_bounds: true,
            max_rotation,
        }
    }

    /// Create a TubeAlgorithm with full configuration control.
    pub fn with_config(config: TubeAlgorithmConfig) -> Self {
        Self {
            use_rotation_cutoffs: config.use_rotation_cutoffs,
            use_action_bounds: config.use_action_bounds,
            max_rotation: config.max_rotation,
        }
    }
}

impl CapacityAlgorithm for TubeAlgorithm {
    fn metadata(&self) -> AlgorithmMetadata {
        AlgorithmMetadata {
            name: "Tube (CH2021)",
            description: "Branch-and-bound search over tube compositions",
            requires_non_lagrangian: false,
            lagrangian_product_only: false,
            complexity: "O(F! / pruning)",
            max_recommended_facets: Some(20),
        }
    }

    fn supports_input(&self, hrep: &PolytopeHRep) -> Result<(), String> {
        hrep.validate(1e-6).map_err(|e| e.to_string())
    }

    fn compute(&self, hrep: PolytopeHRep) -> Result<CapacityResult, AlgorithmError> {
        let config = TubeAlgorithmConfig {
            max_rotation: self.max_rotation,
            use_rotation_cutoffs: self.use_rotation_cutoffs,
            use_action_bounds: self.use_action_bounds,
        };
        compute_capacity_with_config(hrep, config)
    }
}

/// Placeholder for the HK2019 quadratic programming algorithm.
#[derive(Clone, Debug, Default)]
pub struct HK2019Algorithm {
    pub tolerance: f64,
}

impl HK2019Algorithm {
    pub fn new() -> Self {
        Self { tolerance: 1e-8 }
    }
}

impl CapacityAlgorithm for HK2019Algorithm {
    fn metadata(&self) -> AlgorithmMetadata {
        AlgorithmMetadata {
            name: "HK2019 (QP)",
            description: "Quadratic programming formulation",
            requires_non_lagrangian: false,
            lagrangian_product_only: false,
            complexity: "O(F!) where F is the number of facets",
            max_recommended_facets: Some(8), // 9+ times out at 60s
        }
    }

    fn supports_input(&self, hrep: &PolytopeHRep) -> Result<(), String> {
        hrep.validate(1e-6).map_err(|e| e.to_string())?;
        let num_facets = hrep.normals.len();
        if num_facets > 10 {
            return Err(format!(
                "HK2019 becomes very slow for >10 facets (have {})",
                num_facets
            ));
        }
        Ok(())
    }

    fn compute(&self, hrep: PolytopeHRep) -> Result<CapacityResult, AlgorithmError> {
        crate::hk2019::compute_hk2019_capacity(hrep)
    }

    fn timeout_hint_ms(&self, hrep: &PolytopeHRep) -> Option<u64> {
        let facets = hrep.normals.len();
        // Factorial complexity: 8! = 40320, 10! = 3.6M
        let factorial: u64 = (1..=facets as u64).product();
        Some((factorial / 1000).max(100).min(300000))
    }
}

/// Minkowski billiard algorithm for Lagrangian products (LP-based).
///
/// For K = K₁ × K₂ where K₁ ⊂ ℝ²_q and K₂ ⊂ ℝ²_p, the EHZ capacity
/// equals the minimal length of a closed K₂°-billiard trajectory in K₁.
///
/// **Citation**: Thesis §algorithm-billiard-spec.md establishes the billiard-capacity
/// correspondence for Lagrangian products.
///
/// Uses linear programming to find the optimal trajectory.
/// **Citation**: Rudolf 2022 Theorem 4 states optimal has at most 3 bounces for 2D polygons.
/// UNCITED in existing materials: Need to verify Rudolf 2022 citation is in references.bib.
#[derive(Clone, Debug, Default)]
pub struct MinkowskiBilliardAlgorithm;

impl MinkowskiBilliardAlgorithm {
    pub fn new() -> Self {
        Self
    }
}

impl CapacityAlgorithm for MinkowskiBilliardAlgorithm {
    fn metadata(&self) -> AlgorithmMetadata {
        AlgorithmMetadata {
            name: "Minkowski Billiard (LP)",
            description: "LP-based billiard dynamics for Lagrangian products",
            requires_non_lagrangian: false,
            lagrangian_product_only: true,
            // Complexity: O(n³·m) where n = edges of K₁, m = vertices of K₂
            // - C(n,2) + C(n,3) = O(n³) edge pairs/triples
            // - Each LP has O(m) constraints and O(1) variables
            complexity: "O(n³·m) for n edges in K₁, m vertices in K₂",
            max_recommended_facets: None,
        }
    }

    fn supports_input(&self, hrep: &PolytopeHRep) -> Result<(), String> {
        hrep.validate(1e-6).map_err(|e| e.to_string())?;
        // Check if it's a Lagrangian product
        let is_lagrangian_product = hrep.normals.iter().all(|n| {
            let qpart = (n[0].abs() > 1e-10) || (n[1].abs() > 1e-10);
            let ppart = (n[2].abs() > 1e-10) || (n[3].abs() > 1e-10);
            (qpart && !ppart) || (!qpart && ppart)
        });

        if !is_lagrangian_product {
            return Err(
                "MinkowskiBilliard only works for Lagrangian products (K = K₁ × K₂)".to_string(),
            );
        }
        Ok(())
    }

    fn compute(&self, hrep: PolytopeHRep) -> Result<CapacityResult, AlgorithmError> {
        crate::billiard_lp::compute_billiard_capacity_lp(hrep)
    }

    fn timeout_hint_ms(&self, _hrep: &PolytopeHRep) -> Option<u64> {
        Some(100)
    }
}

/// Collection of all available algorithms.
pub fn all_algorithms() -> Vec<Box<dyn CapacityAlgorithm>> {
    vec![
        Box::new(TubeAlgorithm::new()),
        Box::new(HK2019Algorithm::new()),
        Box::new(MinkowskiBilliardAlgorithm::new()),
    ]
}
