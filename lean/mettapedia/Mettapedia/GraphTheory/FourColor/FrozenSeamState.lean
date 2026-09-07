import Mettapedia.GraphTheory.FourColor.FrozenVertexSideCount
import Mettapedia.GraphTheory.FourColor.FrozenJointReindex
import Mettapedia.GraphTheory.FourColor.MarkedSeamState

/-! # A finite seam state retaining frozen-colour correlations

The additional component records the joint support of the complete cut
word and all prescribed colours. Its carrier depends only on the width
and the number of named darts, never on the size of the ambient map.
-/

namespace Mettapedia.GraphTheory.FourColor.FrozenSeamState

open GoertzelV24NormalizedTaitSupport GoertzelV24MajorityShoreNormalizedState
open GoertzelV24RotationCutDartDecomposition GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24VertexSideOpenTangle
open FrozenVertexSideCount FrozenJointReindex

noncomputable section
universe u v
attribute [local instance] Classical.propDecidable
variable {M : Type v}

abbrev State (M : Type v) (k : ℕ) :=
  MarkedSeamState.Marked.{u} M k × Set ((StandardPort.{u} k → Color) × (M → Color))

abbrev Bounded (M : Type v) (k : ℕ) := Σ j : Fin (k + 1), State.{u} M j.val

def stateBound (k t : ℕ) : ℕ := MarkedSeamState.stateBound k t * 2 ^ (4 ^ (k + t))

theorem card_joint [Fintype M] (k : ℕ) :
    Fintype.card (Set ((StandardPort.{u} k → Color) × (M → Color))) =
      2 ^ (4 ^ (k + Fintype.card M)) := by
  simp [StandardPort, Color, F2, pow_add]

theorem card_bounded_le [Fintype M] (k : ℕ) :
    Fintype.card (Bounded.{u} M k) ≤ stateBound k (Fintype.card M) := by
  have hcard (j : ℕ) : Fintype.card (State.{u} M j) =
      Fintype.card (MarkedSeamState.Marked.{u} M j) * 2 ^ (4 ^ (j + Fintype.card M)) := by
    change Fintype.card (MarkedSeamState.Marked.{u} M j ×
      Set ((StandardPort.{u} j → Color) × (M → Color))) = _
    rw [Fintype.card_prod, card_joint]
  rw [Fintype.card_sigma]
  simp only [hcard]
  calc
    _ ≤ ∑ j : Fin (k + 1), Fintype.card (MarkedSeamState.Marked.{u} M j.val) *
        2 ^ (4 ^ (k + Fintype.card M)) := by
      apply Finset.sum_le_sum
      intro j _
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      apply Nat.pow_le_pow_right (by decide : 1 ≤ 4)
      exact Nat.add_le_add_right (Nat.le_of_lt_succ j.isLt) _
    _ = Fintype.card (MarkedSeamState.Bounded.{u} M k) *
        2 ^ (4 ^ (k + Fintype.card M)) := by rw [Fintype.card_sigma, Finset.sum_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (MarkedSeamState.card_bounded_le (M := M) k)

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

def jointOfShore (rotation : SimpleGraphDartRotation.Data G) (shore : Finset G.edgeSet)
    (root : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (mark : M → G.Dart) (k : ℕ) (hw : boundaryWidth rotation shore = k) :=
  joint (innerTangle rotation shore root) (boundaryCoordinate rotation shore k hw).symm
    (sideObservation rotation.toRotationSystem (majorityRetainedKeep G shore) mark)

def ofShore (rotation : SimpleGraphDartRotation.Data G) (shore : Finset G.edgeSet)
    (root : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (mark : M → G.Dart) (k : ℕ) (hw : boundaryWidth rotation shore = k) : State.{u} M k :=
  (MarkedSeamState.ofShore rotation shore root mark k hw,
    jointOfShore rotation shore root mark k hw)

def boundedOfShore (rotation : SimpleGraphDartRotation.Data G) (shore : Finset G.edgeSet)
    (root : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (mark : M → G.Dart) (k : ℕ) (hw : boundaryWidth rotation shore ≤ k) : Bounded.{u} M k :=
  ⟨⟨boundaryWidth rotation shore, by omega⟩, ofShore rotation shore root mark _ rfl⟩

omit [G.LocallyFinite] in
theorem ofShore_ndrec (rotation : SimpleGraphDartRotation.Data G) (shore : Finset G.edgeSet)
    (root : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (mark : M → G.Dart) (k : ℕ) (hw : boundaryWidth rotation shore = k) :
    Eq.ndrec (ofShore rotation shore root mark _ rfl) hw = ofShore rotation shore root mark k hw := by
  cases hw
  rfl

omit [G.LocallyFinite] in
theorem boundedOfShore_eq_elim (rotation : SimpleGraphDartRotation.Data G)
    (old new : Finset G.edgeSet)
    (oldRoot : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G old))
    (newRoot : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G new))
    (mark : M → G.Dart) (k : ℕ)
    (ho : boundaryWidth rotation old ≤ k) (hn : boundaryWidth rotation new ≤ k)
    (heq : boundedOfShore rotation old oldRoot mark k ho =
      boundedOfShore rotation new newRoot mark k hn) :
    ∃ width, ∃ hwOld : boundaryWidth rotation old = width,
      ∃ hwNew : boundaryWidth rotation new = width,
        ofShore rotation old oldRoot mark width hwOld = ofShore rotation new newRoot mark width hwNew := by
  rcases Sigma.ext_iff.mp heq with ⟨hi, hv⟩
  have hw : boundaryWidth rotation old = boundaryWidth rotation new := congrArg Fin.val hi
  refine ⟨boundaryWidth rotation new, hw, rfl, ?_⟩
  rw [← ofShore_ndrec rotation old oldRoot mark _ hw]
  exact eq_of_heq ((eqRec_heq hw (ofShore rotation old oldRoot mark _ rfl)).trans hv)

end
end Mettapedia.GraphTheory.FourColor.FrozenSeamState
