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
    // J*a = (-a[2], -a[3], a[0], a[1]) per thesis definition
    // ω(a, b) = ⟨Ja, b⟩
    -a[2] * b[0] - a[3] * b[1] + a[0] * b[2] + a[1] * b[3]
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

            // Check which facet pairs form 2-faces
            let mut has_2face = vec![vec![false; 8]; 8];
            for tf in &data.two_face_data {
                has_2face[tf.entry_facet][tf.exit_facet] = true;
                has_2face[tf.exit_facet][tf.entry_facet] = true;
            }

            println!("\n=== All pairwise ω values ===");
            println!("Pairs without 2-face may indicate non-adjacent facets (expected) or a bug.");
            for i in 0..8 {
                for j in (i+1)..8 {
                    let omega = symplectic_form(&hrep.normals[i], &hrep.normals[j]);
                    let has_tf = has_2face[i][j];
                    let marker = if !has_tf && omega.abs() > 0.05 { " <-- NO 2-FACE!" } else { "" };
                    println!("ω(n{}, n{}) = {:+.4}, has_2face={}{}", i, j, omega, has_tf, marker);
                }
            }

            // Check specifically facets 3 and 5 (sinks)
            println!("\n=== Investigating sink facets 3 and 5 ===");
            println!("For the lemma to hold, these should have at least one outgoing 2-face.");
            println!("Checking which facets are adjacent to 3:");
            for j in 0..8 {
                if j == 3 { continue; }
                let omega = symplectic_form(&hrep.normals[3], &hrep.normals[j]);
                let has_tf = has_2face[3][j];
                println!("  ω(n3, n{}) = {:+.4} → flow {} (has_2face={})",
                    j, omega, if omega > 0.0 { "3→".to_string() + &j.to_string() } else { j.to_string() + "→3" }, has_tf);
            }

            // Examine facet 3's geometry
            println!("\n=== Facet 3 geometry ===");
            // Find vertices on facet 3 (within tolerance of the hyperplane)
            let n3 = &hrep.normals[3];
            let h3 = hrep.heights[3];
            let eps = 1e-8;
            let facet3_verts: Vec<usize> = data.vertices.iter().enumerate()
                .filter(|(_, v)| (v.dot(n3) - h3).abs() < eps)
                .map(|(i, _)| i)
                .collect();
            println!("Vertices on facet 3: {:?}", facet3_verts);

            // For each vertex on facet 3, which other facets is it on?
            println!("Vertex → facet membership:");
            for &vi in &facet3_verts {
                let v = &data.vertices[vi];
                let on_facets: Vec<usize> = (0..8)
                    .filter(|&f| (v.dot(&hrep.normals[f]) - hrep.heights[f]).abs() < eps)
                    .collect();
                println!("  v{}: on facets {:?}", vi, on_facets);
            }

            // Find edges of facet 3 (pairs of vertices both on facet 3 and on exactly one other facet)
            println!("\nEdges of facet 3 (2-faces that include vertices from facet 3):");
            for &vi in &facet3_verts {
                for &vj in &facet3_verts {
                    if vi >= vj { continue; }
                    let v_i = &data.vertices[vi];
                    let v_j = &data.vertices[vj];
                    // Find common facets (besides 3)
                    let mut common_facets: Vec<usize> = Vec::new();
                    for f in 0..8 {
                        if f == 3 { continue; }
                        let on_i = (v_i.dot(&hrep.normals[f]) - hrep.heights[f]).abs() < eps;
                        let on_j = (v_j.dot(&hrep.normals[f]) - hrep.heights[f]).abs() < eps;
                        if on_i && on_j {
                            common_facets.push(f);
                        }
                    }
                    if common_facets.len() >= 2 {
                        println!("  Edge v{}-v{}: common facets {:?}", vi, vj, common_facets);
                    }
                }
            }

            // Check the triangular faces of facet 3's tetrahedron
            println!("\n=== Triangular faces of facet 3 (tetrahedron check) ===");
            let verts_3 = vec![4usize, 5, 6, 11];
            for i in 0..4 {
                for j in (i+1)..4 {
                    for k in (j+1)..4 {
                        let (vi, vj, vk) = (verts_3[i], verts_3[j], verts_3[k]);
                        let (v_i, v_j, v_k) = (&data.vertices[vi], &data.vertices[vj], &data.vertices[vk]);

                        // Find facets that contain all three vertices (besides 3)
                        let mut shared_facets: Vec<usize> = Vec::new();
                        for f in 0..8 {
                            if f == 3 { continue; }
                            let on_i = (v_i.dot(&hrep.normals[f]) - hrep.heights[f]).abs() < eps;
                            let on_j = (v_j.dot(&hrep.normals[f]) - hrep.heights[f]).abs() < eps;
                            let on_k = (v_k.dot(&hrep.normals[f]) - hrep.heights[f]).abs() < eps;
                            if on_i && on_j && on_k {
                                shared_facets.push(f);
                            }
                        }

                        let status = if shared_facets.is_empty() { "EXPOSED (no 2-face!)" } else { "" };
                        println!("  Triangle v{}-v{}-v{}: shared with facets {:?} {}", vi, vj, vk, shared_facets, status);
                    }
                }
            }
        }
        Err(e) => {
            println!("\n=== Preprocessing FAILED: {} ===", e);
        }
    }
}
