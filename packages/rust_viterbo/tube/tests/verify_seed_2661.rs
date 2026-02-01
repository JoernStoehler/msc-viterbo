//! Verify polytope and 2-face data for seed 2661

use tube::preprocess::preprocess;
use tube::types::PolytopeHRep;
use nalgebra::Vector4;

fn generate_raw_hrep(seed: u64, n_facets: usize) -> PolytopeHRep {
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
    PolytopeHRep::new(normals, heights)
}

fn symplectic_form(a: &Vector4<f64>, b: &Vector4<f64>) -> f64 {
    // J*a = (-a[1], a[0], -a[3], a[2])
    -a[1] * b[0] + a[0] * b[1] - a[3] * b[2] + a[2] * b[3]
}

#[test]
fn verify_2661() {
    let hrep = generate_raw_hrep(2661, 8);
    
    println!("\n=== Raw H-rep normals ===");
    for (i, n) in hrep.normals.iter().enumerate() {
        println!("n{} = ({:+.4}, {:+.4}, {:+.4}, {:+.4})", i, n[0], n[1], n[2], n[3]);
    }
    
    // Try to preprocess
    match preprocess(&hrep) {
        Ok(data) => {
            println!("\n=== Preprocessing succeeded ===");
            println!("Vertices: {}", data.vertices.len());
            println!("2-faces: {}", data.two_face_data.len());
            
            println!("\n=== Actual 2-faces (adjacent facet pairs) ===");
            for (k, tf) in data.two_face_data.iter().enumerate() {
                let ni = &hrep.normals[tf.entry_facet];
                let nj = &hrep.normals[tf.exit_facet];
                let omega_computed = symplectic_form(ni, nj);
                println!(
                    "2-face {:2}: entry={}, exit={}, stored_ω={:.4}, computed_ω={:.4}",
                    k, tf.entry_facet, tf.exit_facet, tf.omega, omega_computed
                );
            }
            
            println!("\n=== Facet entry/exit counts ===");
            let mut as_entry = vec![0usize; 8];
            let mut as_exit = vec![0usize; 8];
            for tf in &data.two_face_data {
                as_entry[tf.entry_facet] += 1;
                as_exit[tf.exit_facet] += 1;
            }
            for i in 0..8 {
                let status = if as_entry[i] == 0 { "SINK" } else if as_exit[i] == 0 { "SOURCE" } else { "" };
                println!("Facet {}: entry_count={}, exit_count={} {}", i, as_entry[i], as_exit[i], status);
            }
        }
        Err(e) => {
            println!("\n=== Preprocessing FAILED: {} ===", e);
        }
    }
}
