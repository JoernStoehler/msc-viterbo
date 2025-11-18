import ProbingViterbo.Symplectic.ClosedCharacteristic
import Mathlib.Topology.Instances.Real

noncomputable section
open scoped BigOperators
open Set

namespace ProbingViterbo
namespace Symplectic

open Geometry

variable {V : Type _} [AddCommGroup V] [Module Real V]
variable [NormedAddCommGroup V] [NormedSpace Real V] [SymplecticSpace V]

/-- Data describing the convex/concave pair in Clarke's duality principle. -/
structure ClarkeDualData (K : StarConvexPolytope V) where
  supportFunction : V -> Real
  polarSupport : V -> Real
  convexity : Prop := True
  coercivity : Prop := True
  dualityGapNonneg : Prop := True

namespace ClarkeDualData

variable {K : StarConvexPolytope V}

/-- The functional that is minimized in the dual problem. -/
def dualFunctional (data : ClarkeDualData K) : V -> Real := data.polarSupport

end ClarkeDualData

/-- Bundle the hypotheses that allow us to turn Clarke duality into combinatorial constraints. -/
structure ClarkeDualityPackage (K : StarConvexPolytope V) where
  data : ClarkeDualData K
  action : ActionFunctional K
  witnessesDuality : Prop := True
  gradientFlowWellPosed : Prop := True

namespace ClarkeDualityPackage

variable {K : StarConvexPolytope V}

/-- Generic bound of the action via the dual functional. -/
theorem action_le_dual (pkg : ClarkeDualityPackage K)
    (γ : ClosedCharacteristic K) :
    pkg.action γ ≤ pkg.data.supportFunction (γ 0) := by
  classical
  sorry

/-- Converse inequality that recovers equality for minimizers. -/
theorem dual_le_action (pkg : ClarkeDualityPackage K)
    (γ : ClosedCharacteristic K) :
    pkg.data.polarSupport (γ 0) ≤ pkg.action γ := by
  classical
  sorry

/-- Main combinatorial consequence used downstream: skeleton visits are intervals. -/
theorem visits_face_on_interval
    (pkg : ClarkeDualityPackage K) {γ : ClosedCharacteristic K}
    (hmin : pkg.action.IsMinimizer γ) (F : K.Face) :
    γ.visitsFaceAtMostOnce F := by
  classical
  sorry

end ClarkeDualityPackage

end Symplectic
end ProbingViterbo
