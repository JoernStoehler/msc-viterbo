//! Print the exact polytope data for seed 2661

use nalgebra::Vector4;

fn main() {}

#[test]
fn print_polytope_2661() {
    let seed = 2661u64;
    let n_facets = 8;

    // Replicate the random_hrep generation exactly
    let mut rng_state = seed;
    let mut next_rand_01 = || {
        rng_state = rng_state.wrapping_mul(6364136223846793005).wrapping_add(1);
        ((rng_state >> 33) as f64) / (u32::MAX as f64)
    };

    let mut next_gaussian_pair = || {
        let u1 = next_rand_01().max(1e-10);
        let u2 = next_rand_01();
        let r = (-2.0 * u1.ln()).sqrt();
        let theta = 2.0 * std::f64::consts::PI * u2;
        (r * theta.cos(), r * theta.sin())
    };

    let mut normals = Vec::with_capacity(n_facets);
    for _ in 0..n_facets {
        let (g1, g2) = next_gaussian_pair();
        let (g3, g4) = next_gaussian_pair();
        let v = Vector4::new(g1, g2, g3, g4);
        normals.push(v / v.norm());
    }

    let heights: Vec<f64> = (0..n_facets).map(|_| 0.3 + next_rand_01() * 2.7).collect();

    println!("\n=== Polytope K (seed 2661, 8 halfspaces) ===");
    println!("K = {{ x ∈ ℝ⁴ : ⟨nᵢ, x⟩ ≤ hᵢ for all i }}\n");
    
    for i in 0..n_facets {
        let n = &normals[i];
        let h = heights[i];
        println!("Halfspace {}: n = ({:+.6}, {:+.6}, {:+.6}, {:+.6}), h = {:.6}",
            i, n[0], n[1], n[2], n[3], h);
    }
    
    // Compute omega for all pairs
    println!("\n=== Symplectic form ω(nᵢ, nⱼ) = ⟨Jnᵢ, nⱼ⟩ ===");
    println!("J = diag(J₂, J₂) where J₂ = [[0, -1], [1, 0]]");
    println!("So Jn = (-n₁, n₀, -n₃, n₂)\n");
    
    for i in 0..n_facets {
        for j in (i+1)..n_facets {
            let ni = &normals[i];
            let nj = &normals[j];
            // J*ni = (-ni[1], ni[0], -ni[3], ni[2])
            let jni = Vector4::new(-ni[1], ni[0], -ni[3], ni[2]);
            let omega = jni.dot(nj);
            if omega.abs() > 0.001 {
                let flow = if omega > 0.0 { format!("{} → {}", i, j) } else { format!("{} → {}", j, i) };
                println!("ω(n{}, n{}) = {:+.6}  (flow: {})", i, j, omega, flow);
            }
        }
    }
}
