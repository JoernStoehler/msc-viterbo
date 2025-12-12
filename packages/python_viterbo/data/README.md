# Data layout (polytopes and experiment inputs)

- `counterexamples/hk-o-2024/` — facet normals/heights for the HK&O counterexample; include JSON with `normals`, `heights`, metadata (coordinate convention `(q1,q2,p1,p2)`, `J(q,p)=(-p,q)`).
- `examples/non-lagrangian/` — a small non-Lagrangian polytope with explicit expected capacity for regression.
- `sanity/cube/` — cube or product bodies for smoke tests.

Conventions:
- Store machine-readable facet data as JSON (`normals`: list of 4-vectors, `heights`: list of scalars, optional `name`, `source`).
- Assets produced from these datasets should be written under `packages/latex_viterbo/assets/<category>/`.
