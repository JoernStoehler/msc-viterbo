//! Debug module for transition matrix investigation
//!
//! This investigates why det(ψ) ≠ 1 when the spec claims it should be 1.

#[cfg(test)]
mod tests {
    use nalgebra::{Vector4, Matrix2, Vector2};
    use crate::geom::{J_MATRIX, K_MATRIX, symplectic_form};
    use crate::trivialization::{trivialize, untrivialize, compute_transition_matrix};

    #[test]
    fn debug_transition_matrix_det() {
        // Test case from my earlier debugging
        let n_i = Vector4::new(1.0, 0.0, 0.0, 0.0);
        let n_j_raw = Vector4::new(0.5, 0.5, 0.5, 0.5);
        let n_j: Vector4<f64> = n_j_raw / n_j_raw.norm();

        println!("n_i = {:?}", n_i);
        println!("n_j = {:?}", n_j);
        println!("||n_j|| = {}", n_j.norm());

        // Check ω(n_i, n_j)
        let omega = symplectic_form(&n_i, &n_j);
        println!("ω(n_i, n_j) = {}", omega);
        println!("Is Lagrangian? {}", omega.abs() < 1e-9);

        // Compute basis vectors
        let jn_i = J_MATRIX * n_i;
        let kn_i = K_MATRIX * n_i;
        let jn_j = J_MATRIX * n_j;
        let kn_j = K_MATRIX * n_j;

        println!("\nJn_i = {:?}", jn_i);
        println!("Kn_i = {:?}", kn_i);
        println!("Jn_j = {:?}", jn_j);
        println!("Kn_j = {:?}", kn_j);

        // Verify Jn_i, Kn_i are orthonormal and perpendicular to n_i
        println!("\nBasis orthonormality for n_i:");
        println!("⟨Jn_i, Kn_i⟩ = {}", jn_i.dot(&kn_i));
        println!("||Jn_i|| = {}", jn_i.norm());
        println!("||Kn_i|| = {}", kn_i.norm());
        println!("⟨Jn_i, n_i⟩ = {}", jn_i.dot(&n_i));
        println!("⟨Kn_i, n_i⟩ = {}", kn_i.dot(&n_i));

        // Compute transition matrix
        let psi = compute_transition_matrix(&n_i, &n_j);
        println!("\nTransition matrix ψ:");
        println!("{}", psi);
        println!("det(ψ) = {}", psi.determinant());
        println!("tr(ψ) = {}", psi.trace());

        // Manual computation
        let col1 = trivialize(&n_j, &jn_i);
        let col2 = trivialize(&n_j, &kn_i);
        println!("\nManual check:");
        println!("τ_{n_j}(Jn_i) = {:?}", col1);
        println!("τ_{n_j}(Kn_i) = {:?}", col2);

        // What does the spec say the transition matrix should be?
        // ψ relates τ_{n_j} coordinates to τ_{n_i} coordinates for vectors on the 2-face
        //
        // Key question: is span(Jn_i, Kn_i) the same as the 2-face tangent space?
        // 2-face tangent space T = {v : ⟨v, n_i⟩ = 0 AND ⟨v, n_j⟩ = 0}

        // Check if Jn_i is in T (perpendicular to both n_i and n_j)
        println!("\nChecking if Jn_i ∈ T(2-face):");
        println!("⟨Jn_i, n_i⟩ = {} (should be 0)", jn_i.dot(&n_i));
        println!("⟨Jn_i, n_j⟩ = {} (should be 0 for Jn_i ∈ T)", jn_i.dot(&n_j));

        println!("\nChecking if Kn_i ∈ T(2-face):");
        println!("⟨Kn_i, n_i⟩ = {} (should be 0)", kn_i.dot(&n_i));
        println!("⟨Kn_i, n_j⟩ = {} (should be 0 for Kn_i ∈ T)", kn_i.dot(&n_j));

        // Note: ⟨Jn_i, n_j⟩ = ω(n_i, n_j) by definition of J
        // So for non-Lagrangian faces, Jn_i is NOT in the 2-face tangent space!

        // The 2-face tangent space T is 2D, and span(Jn_i, Kn_i) is also 2D,
        // but they're different subspaces when ω(n_i, n_j) ≠ 0.
    }

    #[test]
    fn debug_with_adjacent_cross_polytope_normals() {
        // Use normals from the cross-polytope that we know are adjacent
        // Adjacent facets share 3 vertices
        let n_i = Vector4::new(1.0, 1.0, 1.0, 1.0) / 2.0;
        let n_j = Vector4::new(1.0, 1.0, 1.0, -1.0) / 2.0;

        println!("Cross-polytope adjacent normals:");
        println!("n_i = {:?}", n_i);
        println!("n_j = {:?}", n_j);

        let omega = symplectic_form(&n_i, &n_j);
        println!("ω(n_i, n_j) = {}", omega);

        let psi = compute_transition_matrix(&n_i, &n_j);
        println!("\nTransition matrix ψ:");
        println!("{}", psi);
        println!("det(ψ) = {}", psi.determinant());
        println!("tr(ψ) = {}", psi.trace());

        // Check the 2-face tangent space
        let jn_i = J_MATRIX * n_i;
        let kn_i = K_MATRIX * n_i;

        println!("\nChecking if basis vectors are in 2-face tangent space:");
        println!("⟨Jn_i, n_i⟩ = {}", jn_i.dot(&n_i));
        println!("⟨Jn_i, n_j⟩ = {} = ω(n_i, n_j)", jn_i.dot(&n_j));
        println!("⟨Kn_i, n_i⟩ = {}", kn_i.dot(&n_i));
        println!("⟨Kn_i, n_j⟩ = {}", kn_i.dot(&n_j));
    }
}
