import Lake
open Lake DSL

package «docbuild» where
  -- use shared packages dir
  packagesDir := "../.lake/packages"

require «lean_viterbo» from ".."

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.12.0"

@[default_target]
lean_lib Docbuild where
  -- minimal library; docs target provided by doc-gen4 facet

/-- Build docs for the main library only. -/
target docs : FilePath := do
  let pkg ← getPackage "lean_viterbo"
  let some docTarget := pkg.findTarget? (Name.str .anonymous "lean_viterbo:docs")
    | error "lean_viterbo:docs target not found"
  docTarget.fetch
