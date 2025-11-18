import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.StdBasis

noncomputable section
open scoped BigOperators

namespace ProbingViterbo
namespace LinearAlgebra

/-- The ambient real vector space that carries all of our polytopes and flows. -/
abbrev R4 := EuclideanSpace Real (Fin 4)

abbrev phaseSpace : Type := R4

abbrev cotangentSpace : Type := R4

/-- Convenient coordinates that split position/momentum pairs. -/
structure PhasePoint where
  position : Fin 2 -> Real
  momentum : Fin 2 -> Real

namespace PhasePoint

/-- Extensionality principle for phase points. -/
@[ext] lemma ext
    {x y : PhasePoint} (hpos : x.position = y.position)
    (hmom : x.momentum = y.momentum) : x = y := by
  cases x
  cases y
  cases hpos
  cases hmom
  rfl

/-- Embed a phase point into `R^4` using the `[q0, q1, p0, p1]` order. -/
@[simp] def toVector (x : PhasePoint) : R4 := fun
  | ⟨0, _⟩ => x.position ⟨0, by decide⟩
  | ⟨1, _⟩ => x.position ⟨1, by decide⟩
  | ⟨2, _⟩ => x.momentum ⟨0, by decide⟩
  | ⟨3, _⟩ => x.momentum ⟨1, by decide⟩

/-- Project an `R^4` vector to position/momentum coordinates. -/
@[simp] def ofVector (x : R4) : PhasePoint where
  position
    | ⟨0, _⟩ => x ⟨0, by decide⟩
    | ⟨1, _⟩ => x ⟨1, by decide⟩
  momentum
    | ⟨0, _⟩ => x ⟨2, by decide⟩
    | ⟨1, _⟩ => x ⟨3, by decide⟩

@[simp] lemma ofVector_toVector (x : PhasePoint) : ofVector (toVector x) = x := by
  cases x
  apply PhasePoint.ext
  · funext i
    fin_cases i <;> simp [PhasePoint.ofVector, PhasePoint.toVector]
  · funext i
    fin_cases i <;> simp [PhasePoint.ofVector, PhasePoint.toVector]

@[simp] lemma toVector_ofVector (x : R4) : (ofVector x).toVector = x := by
  funext i
  fin_cases i <;> simp [PhasePoint.ofVector, PhasePoint.toVector]

end PhasePoint

/-- Standard coordinate basis of `R^4`. -/
abbrev coordinateBasis : Basis (Fin 4) Real R4 := Pi.basisFun Real _

end LinearAlgebra
end ProbingViterbo
