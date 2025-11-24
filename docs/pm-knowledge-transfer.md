# PM Knowledge Transfer (scratchpad)
Drafting ground for you to dump everything you remember from the prototype. Keep it quick, unordered, and biased toward facts/decisions. I will annotate gaps and then distill into roadmap + issues.

## 1) Outcomes and scope
- Thesis submission target date: 6mo after start date
- Submission format expectations (PDF, site, artifacts): pdf + code repo
- Definition of “done” for the algorithm/library: 
  - Rust: basic types and functions for symplectic geometry e.g. convex polytope representation, volume, EHZ capacity, systolic ratio (right convention!), with unit tests and benchmarks and profiling info, and instrumented debug versions to e.g. trace search behavior, in addition to a non-instrumented production version for large datasets.
  - Lean4: formalization of basic symplectic geometry, the main theorems, including a theorem that our algorithm is correct; ideally, the algorithm is runnable from Lean4, e.g. with real/rational numbers, though that's more of an extra. Code comments explain the proofs on a high level to a reader who's not super familiar with Lean4.
  - Python: maturin runs, in Rust there's a PyO3 interface crate. 
  - Thesis: similar to what's in Lean4 & in Rust, but handwritten for the final thesis reader (a typical mathematician). Optionally this can be generated from Lean4 comments, e.g. with doc-gen4 or sth, or it's a manually maintained copywrite.
  - The Lean4, Rust, Thesis versions of the algorithm need to match closely, so that verification in Lean4 is believed to be good evidence about the Rust implementation. Rust additionally to the (weaker-than-Lean4) static typechecking also has unit tests. We optimize for performance in Rust, so getting to this done state may involve changing the algorithm a bit, which involves changing the thesis + lean4 versions as well.
  - Benchmarks include ablation studies for optimization choices.
  - We also want the existing literature's algorithms in Rust, just to compare performance and verify correctness. Since we base of CH2021 that will be easier than HK2019, but also less valuable for comparison.
  - Python needn't unit test what Rust already unit tests, instead we just want an integration test that shows that the Python interface works at all. Basic pyright typechecking also can tell us when we e.g. have changed the Rust interface, and the pyo3 wrapper, but forgot to update Python code that uses the maturin generated module.
- Definition of “done” for experiments/datasets:
  - Experiments can always be picked up and continued; done usually means that we do no longer prioritize working on them, e.g. we got our insights AND wrote them up. 
  - So the main aspects worth repeating here are: we don't want to just do a calculation and delete it, we want to record it for later reproduction or later extension/modification. We are okay if experiments after e.g. library changes enter a broken state that requires simple straightforward fixes, but we want to at least schedule an issue to modernize the experiment so by the end of the thesis we will have remembered to do so and not forgotten/postponed it indefinitely.
  - We also want to document experiments, e.g. in the form of a namespace module docstring for code-specific aspects such as architecture and knobs and learnings on the implementation side, and in the form of markdown files in the thesis that document the idea, plan, results, and interpretation of the experiment. As usual, we try to keep the whole latest commit up-to-date and self-contained, or at least add a gh issue to fix outdated writeups later.
  - We don't use custom commands or even ad-hoc multiline bash/python commands to run our experiments. Mayybe during rapid prototyping but by the time we commit, and definitely by the time we consider an experiment done-for-now, there should be canonical commands such as "uv run python -m viterbo.experiments.foo.stage_run --config data/configs/foo/production.json"; We can use a packages/python_viterbo/scripts/reproduce-all-experiments.sh script that runs in sequence all experiments without knobs, which is never executed but in-principle executable and serves as a concise reference for how to run all our experiments, and in particular, in what order so dependencies don't error.
  - We use git lfs for data and other artifacts that are worth versioning/worth sharing and isolating across worktrees.
  - /workspaces/worktrees/shared/ is also available for sharing files globally across worktrees, but not versioned and not with per-worktree copies. So git lfs is just usually the way-to-go.
  - All artifacts ofc have a git commit that tells us alongside what code version changes they were committed. This way we can (manually) catch stale data. Tasks have to involve a step to rerun affected pipelines and commit the changed artifacts alongside or after the code changes for this to meaningful.

## 2) Milestones you already had
- List any milestone names/dates you used before, even if rough.
  - See 00-overview.mdx roadmap section and come back to me once you copied that over. I wrote 00- a bit quickly, so you can maybe break down items more clearly instead of long multi-item lines.

## 3) Algorithm details from the prototype
- Data structures (polytope representation, normals, cones):
  - Rust
    - always f64, nalgebra; we only care about 4d convex polytopes and we demand "high-quality" types, e.g. guaranteeing certain constraints during construction time instead of having multiple types for different constraints.
    - 4D Polytope:
        - H-rep: normals and offsets (4 dim; var number of halfspaces; type promise: non-redundant, non-degenerate, convex, contains 0 in interior)
          - normals $n$ have $||n|| = 1$ and point outwards
          - offsets btw fulfill $\langle x, n \rangle \leq d$ for all $x$ in the polytope and $h_K(n) = d$
          - bc star-shaped: $d > 0$ for all halfspaces
        - V-rep: vertices (4 dim; var number of vertices; type promise: no extra vertices in the interior or on the convex hull i.e. non-redundant; non-degenerate i.e. not all on a hyperplane; convex is guaranteed that way, but we also demand star-shaped i.e. contains 0 in interior)
        - incidence: given H-rep and V-rep, we can say what vertex lies on what faces;
        - skeleton: list of 3-faces, 2-faces, 1-faces, 0-faces (vertices), with adjacency info
    - 3D Face:
        - a normal and offset from the H-rep
        - a list of vertices from the V-rep
        - the velocity on the face $v = \frac{2}{d} J n$ where $n$ is the face normal and $d$ the offset
        - assumption: 3-faces are non-empty
    - 2D Face:
        - two normals and offsets from the H-rep (<=> two 3-faces)
        - a list of vertices from the V-rep
        - a bool whether the face is lagrangian
        - if not lagrangian: an orthogonal symplectic basis $u,v \in \mathbb{R}^4$ with $\langle u , J v \rangle = 1$ and $\langle u, v \rangle = 0$; also an arbitrary origin point in the interior of the 2-face
        - else: an orthogonal basis, an arbitary origin point in the interior of the 2-face
        - if not lagrangian: one of the two 3-faces has a velocity pointing into the 2-face, the other out of the 2-face; we store which is which (by letting former be the first in the index tuple)
        - if not lagrangian: for the source 3-face: the projection matrix from $\mathbb{R}^4$ to $\mathbb{R}^2$ along the velocity direction onto the 2-face plane, using its symplectic basis and some arbitrary origin point
        - assumption: 2-faces are non-empty
    - 1D Face: not needed
    - 0D Face: not needed, or rather, we already have a V-rep
    - important: we don't need to store all this in public types; in fact, we mostly move around polytopes as either H-rep or V-rep only, and then compute on demand the other rep, the skeleton etc.
    - we do need a function that quickly spits out the skeleton, mostly as (H-rep, V-rep, which-vertices-and-half-spaces-make-up-each-face)
    - we can then enrich all the other data on demand from other functions
    - our algorithm builds some graph structures with attached data, so like, with lots of internal stuff to define and shuffle around; we'll get there eventaully, this repo hopefully is a lot cleaner than the last one
- Search/pruning rules (rotation bounds, action bounds, symmetry breaking):
    - rotation; we have a theorem that $CZ=3$, i.e. $1<rho<2$, for some minimum action orbit; so that's where we look; increments of rotation are non-negative, so we can prune as soon as we hit $rho >= 2$
    - action bounds; we start with an upper bound from an enclosing ball; we dynamically adjust the upper bound whenever we find a new candidate for minimum action orbit, and prune branches that exceed the current upper bound; this again uses that the action is monotone; note that branches only provide a lower bound action, so we compare lower bound of branch vs upper bound from best candidate, and at the end have a fixed-point step that gives the actual value instead of the lower bound; the lower bound increases the deeper we go, bc as said non-negative increments, so we can prune branches;
    - sadly lagrangian faces are weird and require extra-careful handling; we will for now focus on polytopes without lagrangian 2-faces; if we have lagrangian 2-faces, we error; the caller can choose to on error perturb the polytope a bit or whatever; so evne for lagrangian case we can obtain due to continuity a very close approximation; the problem may be here that nearly-lagrangian 2-faces are numerically unstable; another problem may be that different perturbations result in hugely different orbits though the approx same action; this is a strong hint that we will have numerical instability issues as well;
    - no symmetry handling nor breaking; this may be useful to ensure full genericity, or avoid certain sources of numerical instability, but nothing we plan now.
- Degeneracy handling (Lagrangian faces, 1-face exclusions, perturbation policy):
    - see above
- Numerical tolerances (eps values, scaling/normalization steps):
    - yep, we define eps values (no need to be configurable), and watch out for float comparisons; tentatively, we will want to be e.g. conservative and permit slightly larger actions than the current upper bound, and when tracking the 2d trajectory candidate sets, we technically allow slightly negative area branches to avoid excluding valid candidates due to rounding; usually we shouldn't get close to epsilon here, so (confirmable via instrumentation and unit tests and profiling and ablation) we don't loose too much performance from not pruning such branches earlier.
    - most quantities will be O(1).
- Known fast/slow paths; hotspots:
    - we have a lot of combinatorical search tree nodes, so we have to precompute hwatever we can, including to keep intermediate results on the stack
    - similarly we use known shapes + nalgebra optimizations in the inner part of the search loops
    - we ablate, i am not sure yet if e.g. heuristics to prioritize certain nodes cost more than they help.
- Validation examples with expected capacities/systolic ratios:
    - pls look them up, i don't want to type them by hand; basis simplex (translated so it contains the 0 in the interior, not as a vertex), the hypercube, the crosspolytope, the standard viterbo counterexample (pentagon x_L 90° rotated pentagon), maybe more. The simplex iirc has sys=3/4, the viterbo counterexample sth >1, the rest ofc <= 1 


## 4) Datasets and assets
- Benchmark polytopes (where to find them, formats):
  - the polytopes with known systolic ratios are useful as unit tests for correctness
  - for performance benchmarks, we can generate random polytopes with various properties (usually: number of halfspaces matters for performance), and ofc edge cases such as (near-) lagrangian 2-faces
  - the standard viterbo counterexample (HK2024) is roughly sth we want to be able to compute in $<100$ ms so that our largest dataset of $10^6$ polytopes can be done in $10^5$ s = a day or so;
  - there's different ways to do random polytopes; basic first distribution would be to take random halfspaces with normals uniform on the sphere and offsets uniform in [0.5, 2.0] or sth; we can do rejection sampling, i.e. resample whenever a polytope is not compact, not convex, not star-shaped, has near/exact lagrangian 2-faces, is redundant, etc. roughly aim stochastically for volume = O(1) so that at least that aspect of the numerics is stable; So, like, $10^-2$ to $10^2$ volume are perfectly fine, but we wouldn't want the weirdness of very flat/small/huge polytopes beyond that.
  - for property unit tests, we can also take known polytopes and perturb them (=> continuity of action & volume in the H-rep data), or apply symplectomorphisms (=> invariance of systolic ratio).
- Generated datasets (size, schema, how to recreate):
  - final largest dataset: 10^6 random polytopes from different families, as well as enumerated polytopes (e.g. n-gon x_L p/q-rotated m-gon for small n,m,p,q)
  - test dataset: one polytope per family, just to test the code paths in both Rust, and in downstream experiments that use the test dataset
  - other datasets: often specific to some family, e.g. only simplices, or only centrally symmetric polytopes, or only the enumerated polytopes; these are useful for specialized experiments, or experiments that want a subset of the data without shuffling the largest dataset, or while we don't have a largest dataset or don't have some sampler families implemented we can use smaller versions;
- Figures/plots (figure IDs, scripts, seeds):
  - git commit is usually enough provisioning
  - we use a packages/thesis/assets/ folder (or similar?) to store static and dynamic assets; committed alongside code changes that generated them, so provisioning can just look at git blame etc.
  - visualizations are generated by the python data science pipeline, using e.g. matplotlib, plotly, ...; 
  - we can also use custom glue code (mdx, ts, astro) to define custom visualizations not in python but in the docs site directly; can be useful for e.g. figure size/layout tuning without having to split up the python pipeline and mix viz + data generation code.
- Experiment configs (config files, hyperparameters):
  - we use a folder (mayybe packages/python_viterbo/data/configs/) to store parameters that the pipelines consume; that's just more easily documented and compared than having them inline in code, or having them in ephemeral bash commands that get lost and forgotten
  - we use different json config files to allow running the same pipeline with different parameters, usually at least a production and test config per experiment
  - the datasets/artifacts produced by production & test configs in the pipelines can be used by python tests as fixtures; e.g. to catch regressions where a pipeline changed some column names in its output csv, without detecting that the test (& other consumers!) have to be updated as well.
- Dataset pipelines can import code from each other; the viterbo.experiments.<name>.<file>.py and viterbo.experiments.<name>.stage_<step>.py pattern is useful imo; stage_ signifies that it's a valid entry point for `uv run python -m viterbo.experiments.<name>.stage_<step> --config <file>.json`.

## 5) Proof / Lean status
- Which lemmas were proved vs. assumed:
  - Lean4 mathlib sadly has very little diffgeo and symplectic geo and polytopes; so we have to formalize a lot of basic lemmas ourselves, and pick good (bundled) types
  - we do have linear algebra at least :)
  - we mostly just formalize and then axiomatically assume various lemmas about smooth symplectic geometry, and the limit of smooth symplectic geometry to polytopes; we use a thesis writeup and references to papers to justify the formalization choices & non-formal proofs
  - what we want to prove is that given some fairly basic statements about symplectic geometry on polytopes (assuming non-lagrangian 2-faces for the input), that our algorithm (using real numbers) indeed computes the EHZ capacity and a minimum orbit correctly; ideally this involves proving some theorems that e.g. the action is monotone, there exists a minimum orbit that visits every 3-face at most once, the normal definition of CZ index matches our computational definition / algorithm subroutine, ...
- Certificates/checkers you had (or planned):
  - ideally we have a Lean4 runnable algorithm that's slow (100s instead of 100ms) but spits out the (rational) EHZ capacity regardless for (perhaps a bit smaller, i.e. $<10$ halfspaces) polytopes; this can be used to compare the Rust implementation not just code-line-by-code-line manually, but also unit test against more (one-time) verified examples
  - certificates for the minimum action are hard to do, since they'd need to show that the pruning of the search tree was done right, which is basically the same as running the whole algorithm again with the initial upper bound being the final action found; so not super useful

## 6) Decisions & rationale to preserve
- Key design choices (why we rejected alternatives):
  - We worked a lot on our algorithm until we found one that looks good and runs for the standard viterbo counterexample fast enough
  - Rust is needed for high performance; it's easier to write than C++;
  - Lean4 is an idea for a bit more certainty and to avoid hidden bugs in the algorithm design that we don#t catch when just writing Rust code and thesis text
  - Python is the glue needed for rapid prototyping of data science experiments, and for easy visualization and data handling
  - Astro.js gives us some nice help with visualization and docs formatting
  - since we use AI agents for most work, we need 0 onboarding for all the above tools! Jörn is also familiar with all of them, though he's rather new to Lean4 and hasn't written much Lean4 himself
- Risky assumptions or open problems:
  - Risky: Lean4 use could be detrimentally costly instead of being the high-trust feedback signal that we sought to get
  - Risky: Numerical instability could mean we have to restrict the input polytopes more than we hoped
  - Risky: Keeping several versions of our algorithm in sync requires discipline and time expense (Thesis, Lean4, Rust)
  - Risky: Having so many independent experiments can lead to them breaking easily when the library, or the experiments changes; we intentionally ignore DRY to avoid tight coupling, but it's still risky

## 7) Open questions for me to resolve
- List anything you want me to clarify/specify/decide after reading this dump.
  - N/A yet; you can see where I need you to read the literature real quick and fill in the gaps (with citations for the future)

## 8) Things to not forget
- Dependencies/tools we must keep aligned:
  - I put a lot of effort into the repo scaffold, so it should be fine (?)
- External references (papers/sections) that anchor our statements:
  - see worktrees/shared/arxiv-store/ for a few papers
  - I will copy over the full reading list for this project that I accumulated
  - 


You can btw take a look (clone into shared/ maybe?) at the previous prototype repos at https://github.com/JoernStoehler/rust-viterbo and /msc-math-viterbo
Both are now abandoned ofc.
