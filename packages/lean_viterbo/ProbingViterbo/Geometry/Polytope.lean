import Mathlib.Analysis.Convex.Star
import Mathlib.Topology.MetricSpace.Basic
import ProbingViterbo.LinearAlgebra.R4

noncomputable section
open scoped BigOperators

namespace ProbingViterbo
namespace Geometry

section

variable (V : Type _) [NormedAddCommGroup V] [NormedSpace Real V]

/-- Data for a compact, star-convex polytope with a distinguished basepoint. -/
structure StarConvexPolytope : Type _ where
  carrier : Set V
  basepoint : V
  nonempty : carrier.Nonempty
  isCompact : IsCompact carrier
  convex : Convex Real carrier
  starConvex : StarConvex Real basepoint carrier
  piecewiseSmoothBoundary : Prop := True

end

namespace StarConvexPolytope

variable {V : Type _} [NormedAddCommGroup V] [NormedSpace Real V]

instance : Coe (StarConvexPolytope V) (Set V) := ⟨fun K => K.carrier⟩

@[simp] lemma coeCarrier (K : StarConvexPolytope V) : (K : Set V) = K.carrier := rfl

/-- Topological boundary of the polytope. -/
def boundary (K : StarConvexPolytope V) : Set V := frontier (K : Set V)

/-- Abstract face data used to refer to skeleton strata. -/
structure Face (K : StarConvexPolytope V) where
  carrier : Set V
  subset_carrier : carrier ⊆ (K : Set V)
  affineDim : Nat
  convex : Convex Real carrier
  supportingHyperplane : Prop := True

namespace Face

/-- Dimension accessor. -/
abbrev dim (K : StarConvexPolytope V) (F : Face K) : Nat := F.affineDim

end Face

/-- `k`-skeleton of a polytope, described via the abstract face type. -/
def skeleton (K : StarConvexPolytope V) (k : Nat) : Set V :=
  {x | x ∈ (K : Set V) ∧ ∃ F : Face K, F.affineDim ≤ k ∧ x ∈ F.carrier}

lemma mem_skeleton_iff (K : StarConvexPolytope V) {k : Nat} {x : V} :
    x ∈ K.skeleton k ↔ x ∈ (K : Set V) ∧ ∃ F : Face K, F.affineDim ≤ k ∧ x ∈ F.carrier :=
  Iff.rfl

/-- Convenience predicate for the set-theoretic boundary. -/
def OnBoundary (K : StarConvexPolytope V) (x : V) : Prop := x ∈ K.boundary

end StarConvexPolytope

end Geometry
end ProbingViterbo
