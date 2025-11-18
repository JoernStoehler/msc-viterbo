import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Topology.Instances.Real
import ProbingViterbo.Geometry.Polytope

noncomputable section
open scoped BigOperators
open Set
open LinearMap

namespace ProbingViterbo
namespace Symplectic

variable (V : Type _) [AddCommGroup V] [Module Real V]

/-- Minimal interface for a symplectic vector space. -/
class SymplecticSpace (V : Type _) [AddCommGroup V] [Module Real V] where
  form : LinearMap.BilinForm Real V
  isAlt : form.IsAlt
  nondegenerate : form.Nondegenerate

attribute [simp] SymplecticSpace.isAlt

namespace SymplecticSpace

variable {V}

/-- Accessor for the symplectic bilinear form. -/
@[simp] def symplecticForm (V : Type _) [AddCommGroup V] [Module Real V]
    [S : SymplecticSpace V] : LinearMap.BilinForm Real V := S.form

lemma symplecticForm_isAlt (V : Type _) [AddCommGroup V] [Module Real V]
    [S : SymplecticSpace V] :
    (symplecticForm (V := V)).IsAlt := S.isAlt

lemma symplecticForm_nondegenerate (V : Type _) [AddCommGroup V] [Module Real V]
    [S : SymplecticSpace V] :
    (symplecticForm (V := V)).Nondegenerate := S.nondegenerate

end SymplecticSpace

variable {V} [SymplecticSpace V]
variable [NormedAddCommGroup V] [NormedSpace Real V]

open Geometry

/-- Closed characteristics that live on the boundary of a star-convex polytope. -/
structure ClosedCharacteristic (K : StarConvexPolytope V) where
  period : Real
  period_pos : 0 < period
  curve : Real -> V
  regularity : Prop := True
  periodic : ∀ t, curve (t + period) = curve t
  onBoundary : ∀ t, curve t ∈ K.boundary
  tangencyCondition : Prop := True

namespace ClosedCharacteristic

variable {K : StarConvexPolytope V}

instance : CoeFun (ClosedCharacteristic K) (fun _ => Real -> V) :=
  ⟨fun γ => γ.curve⟩

@[simp] lemma periodic_eval (γ : ClosedCharacteristic K) (t : Real) :
    γ (t + γ.period) = γ t := γ.periodic t

/-- Raw set of times at which a characteristic lies on a face. -/
def faceTimes (γ : ClosedCharacteristic K) (F : K.Face) : Set Real :=
  {t | γ t ∈ F.carrier}

/-- Being supported on a single connected time interval (modulo period). -/
def visitsFaceAtMostOnce (γ : ClosedCharacteristic K) (F : K.Face) : Prop :=
  ∃ I : Set Real, IsPreconnected I ∧ faceTimes γ F = I

end ClosedCharacteristic

/-- Abstract action functional used for the Ekeland-Hofer-Zehnder capacity. -/
structure ActionFunctional (K : StarConvexPolytope V) where
  toFun : ClosedCharacteristic K -> Real
  measurable : Prop := True
  invariantUnderTimeShift : Prop := True

namespace ActionFunctional

variable {K : StarConvexPolytope V}

instance : CoeFun (ActionFunctional K) (fun _ => ClosedCharacteristic K -> Real) :=
  ⟨fun Φ => Φ.toFun⟩

@[simp] lemma apply (Φ : ActionFunctional K) (γ : ClosedCharacteristic K) : Φ γ = Φ.toFun γ := rfl

noncomputable def infValue (Φ : ActionFunctional K) : Real := sInf (Set.range Φ)

/-- Minimality for the action functional. -/
def IsMinimizer (Φ : ActionFunctional K) (γ : ClosedCharacteristic K) : Prop :=
  ∀ γ', Φ γ ≤ Φ γ'

lemma eq_of_IsMinimizer {Φ : ActionFunctional K} {γ γ' : ClosedCharacteristic K}
    (hγ : Φ.IsMinimizer γ) (hγ' : Φ.IsMinimizer γ') : Φ γ = Φ γ' := by
  have h1 := hγ γ'
  have h2 := hγ' γ
  exact le_antisymm h1 h2

end ActionFunctional

/-- Placeholder for the combinatorial statement used in later Lean developments. -/
theorem minimalCharacteristic_visits_faces_once
    {K : StarConvexPolytope V} (Φ : ActionFunctional K)
    (γ : ClosedCharacteristic K) (hmin : Φ.IsMinimizer γ)
    (hdual : Prop := True) (F : K.Face) :
    γ.visitsFaceAtMostOnce F := by
  classical
  sorry

end Symplectic
end ProbingViterbo
