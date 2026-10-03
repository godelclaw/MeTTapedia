import MettapediaFourColor.InducedGraphRotation

/-! # Surviving face steps in an induced graph

A face step is unchanged whenever its ambient successor is retained.
The equality concerns actual graph darts, through the induced inclusion.
-/

namespace FourColor.InducedGraphRotation

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open PermutationFirstReturnRestriction

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (keep : Set V)

def includeDart (d : (G.induce keep).Dart) : G.Dart := (darts keep d).val

theorem includeDart_injective : Function.Injective (includeDart keep (G := G)) := by
  intro a b h
  exact (darts keep).injective (Subtype.ext h)

theorem phi_of_retained (data : Data G) (outer : (G.induce keep).Dart)
    (d : (G.induce keep).Dart)
    (h : retained keep (data.toRotationSystem.phi (includeDart keep d))) :
    includeDart keep ((rotation keep data outer).toRotationSystem.phi d) =
      data.toRotationSystem.phi (includeDart keep d) := by
  exact nextHit_apply_of_step data.vertexRotation (retained keep)
    (darts keep d.symm) h

end
end FourColor.InducedGraphRotation
