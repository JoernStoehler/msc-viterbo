import Lake
open Lake DSL

package «lean_viterbo» where
  -- Lean project configuration lives here; extend as we add tooling.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.12.0"

@[default_target]
lean_lib ProbingViterbo where
  -- Individual modules sit under the ProbingViterbo namespace.
