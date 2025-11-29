import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace ProbingViterbo

/-- A minimal sanity check to keep the build and docs pipelines exercised. -/
def hello : String := "hello, Lean 4.25"

/-- A tiny lemma to ensure the mathlib environment is available. -/
theorem two_add_two : (2 : ℝ) + 2 = 4 := by norm_num

end ProbingViterbo
