import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin

/-
# Symplectic primitives (Chapter 02-math, “Symplectic preliminaries”)

Lean encodes the ambient phase space as `R4 := EuclideanSpace (Fin 4) ℝ`
with coordinate order `(q₁,q₂,p₁,p₂)`. The standard almost complex
structure `J` and symplectic form `ω(x,y)=⟪J x, y⟫` are fixed here and
reused across the polytope and orbit definitions.
-/

noncomputable section

open BigOperators

namespace ProbingViterbo

/-- Ambient space \(\mathbb R^4\) with the standard Euclidean inner product. -/
abbrev R4 := EuclideanSpace ℝ (Fin 4)

/-- Matrix for the standard almost complex structure on \(\mathbb R^4\)
in coordinates `(q₁,q₂,p₁,p₂)`. -/
def JMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ 0,  0, -1,  0;
      0,  0,  0, -1;
      1,  0,  0,  0;
      0,  1,  0,  0 ]

/-- Linear map \(J(q₁,q₂,p₁,p₂)=(-p₁,-p₂,q₁,q₂)\). -/
def J : R4 →ₗ[ℝ] R4 :=
  let e : R4 ≃ₗ[ℝ] (Fin 4 → ℝ) := (EuclideanSpace.equiv (Fin 4) ℝ).toLinearEquiv
  (e.symm.toLinearMap) ∘ₗ Matrix.mulVecLin JMatrix ∘ₗ e.toLinearMap

/-- Symplectic form \(\omega(x,y)=\langle Jx,y\rangle\). -/
def omega (x y : R4) : ℝ := inner (𝕜:=ℝ) (E:=R4) (J x) y

notation "ω" => omega

lemma omega_def (x y : R4) : ω x y = inner (𝕜:=ℝ) (E:=R4) (J x) y := rfl

/-- Liouville 1‑form evaluated on a tangent vector: \(\lambda_x(v)=\tfrac12\langle Jx,v\rangle\). -/
def liouville (x v : R4) : ℝ := (1 / 2 : ℝ) * ω x v

lemma liouville_def (x v : R4) :
    liouville x v = (1 / 2 : ℝ) * inner (𝕜:=ℝ) (E:=R4) (J x) v := rfl

end ProbingViterbo

end
