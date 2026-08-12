import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationCutDartDecomposition

/-!
# Opposite literal boundary darts

Two cut-open regions can be glued along a physical ambient edge only when
their exposed half-edges use opposite ambient darts.  Equality of the
underlying edge alone leaves two possibilities: the two boundary darts may
be the same ambient dart, or they may be alpha-opposites.  This light lemma
reduces the desired orientation to the one endpoint-side fact that rules out
the same-dart alternative.

The lemma is generic cut plumbing.  It neither supplies a source-region
membership fact nor claims that any particular corridor slabs compose.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationCutDartDecomposition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Boundary darts on the same old edge are alpha-opposite when the base
vertex of the first is not retained by the second side.  The extra endpoint
condition excludes the only other dart on that edge, namely the first dart
itself. -/
theorem alpha_eq_of_boundaryDart_edgeOf_eq_of_not_keep_vert
    (RS : RotationSystem V E) (leftKeep rightKeep : V → Prop)
    (left : BoundaryDart RS leftKeep) (right : BoundaryDart RS rightKeep)
    (hedge : RS.edgeOf left.1.1 = RS.edgeOf right.1.1)
    (hnotRightKeep : ¬ rightKeep (RS.vertOf left.1.1)) :
    RS.alpha left.1.1 = right.1.1 := by
  have hleftOn : left.1.1 ∈ RS.dartsOn (RS.edgeOf left.1.1) := by
    simp
  have hrightOn : right.1.1 ∈ RS.dartsOn (RS.edgeOf left.1.1) := by
    simp [RotationSystem.mem_dartsOn, hedge]
  have hpairs := RS.dartsOn_eq_pair_of_mem hleftOn
  have hcases : right.1.1 = left.1.1 ∨
      right.1.1 = RS.alpha left.1.1 := by
    have hmem : right.1.1 ∈ ({left.1.1, RS.alpha left.1.1} : Finset RS.D) := by
      rw [← hpairs]
      exact hrightOn
    simpa using hmem
  rcases hcases with hsame | hopposite
  · exfalso
    apply hnotRightKeep
    rw [← hsame]
    exact right.1.2
  · exact hopposite.symm

end

end GoertzelV24RotationCutDartDecomposition

end Mettapedia.GraphTheory.FourColor
