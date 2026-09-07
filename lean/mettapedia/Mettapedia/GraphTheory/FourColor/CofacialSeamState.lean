import Mettapedia.GraphTheory.FourColor.FrozenSeamState
import Mettapedia.GraphTheory.FourColor.NamedOpenFace

/-! # Frozen Count states refined by named cofaciality

The return component records all ports and persistent dart names of one
actual shore. Its finite bound charges the number of names, not the lengths
of their faces. The existing joint-colour and structural state is retained.
-/

namespace Mettapedia.GraphTheory.FourColor.CofacialSeamState

open GoertzelV24NormalizedTaitSupport GoertzelV24MajorityShoreNormalizedState
open GoertzelV24RotationCutDartDecomposition GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24VertexSideOpenTangle FrozenVertexSideCount

noncomputable section
universe u v
attribute [local instance] Classical.propDecidable
variable {M : Type v} [Fintype M]

abbrev State (M : Type v) [Fintype M] (k : ℕ) :=
  FrozenSeamState.State.{u} M k × NamedFaceRecord.Record (StandardPort.{u} k ⊕ M)

abbrev Bounded (M : Type v) [Fintype M] (k : ℕ) := Σ j : Fin (k + 1), State.{u} M j.val

def faceBound (k t : ℕ) : ℕ := (k + t).factorial * (k + t + 1) ^ (k + t)

def stateBound (k t : ℕ) : ℕ := FrozenSeamState.stateBound k t * faceBound k t

theorem faceBound_mono {j k : ℕ} (h : j ≤ k) (t : ℕ) : faceBound j t ≤ faceBound k t := by
  apply Nat.mul_le_mul (Nat.factorial_le (Nat.add_le_add_right h t))
  exact (Nat.pow_le_pow_left (by omega : j + t + 1 ≤ k + t + 1) _).trans
    (Nat.pow_le_pow_right (by omega : 1 ≤ k + t + 1) (Nat.add_le_add_right h t))

theorem card_face (k : ℕ) : Fintype.card (NamedFaceRecord.Record (StandardPort.{u} k ⊕ M)) =
    faceBound k (Fintype.card M) := by
  simp [NamedFaceRecord.Record, Fintype.card_perm, StandardPort, faceBound]

theorem card_bounded_le (k : ℕ) :
    Fintype.card (Bounded.{u} M k) ≤ stateBound k (Fintype.card M) := by
  have hcard (j : ℕ) : Fintype.card (State.{u} M j) =
      Fintype.card (FrozenSeamState.State.{u} M j) * faceBound j (Fintype.card M) := by
    change Fintype.card (FrozenSeamState.State.{u} M j ×
      NamedFaceRecord.Record (StandardPort.{u} j ⊕ M)) = _
    rw [Fintype.card_prod, card_face (M := M) j]
  rw [Fintype.card_sigma]
  simp only [hcard]
  calc
    _ ≤ ∑ j : Fin (k + 1), Fintype.card (FrozenSeamState.State.{u} M j.val) *
        faceBound k (Fintype.card M) := by
      apply Finset.sum_le_sum
      intro j _
      exact Nat.mul_le_mul_left _ (faceBound_mono (Nat.le_of_lt_succ j.isLt) _)
    _ = Fintype.card (FrozenSeamState.Bounded.{u} M k) * faceBound k (Fintype.card M) := by
      rw [Fintype.card_sigma, Finset.sum_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (FrozenSeamState.card_bounded_le (M := M) k)

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

def faceOfShore (rotation : SimpleGraphDartRotation.Data G) (shore : Finset G.edgeSet)
    (root : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (mark : M → G.Dart) (k : ℕ) (hw : boundaryWidth rotation shore = k) :=
  NamedOpenFace.record (innerTangle rotation shore root) (boundaryCoordinate rotation shore k hw)
    (sideObservation rotation.toRotationSystem (majorityRetainedKeep G shore) mark)

def ofShore (rotation : SimpleGraphDartRotation.Data G) (shore : Finset G.edgeSet)
    (root : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (mark : M → G.Dart) (k : ℕ) (hw : boundaryWidth rotation shore = k) : State.{u} M k :=
  (FrozenSeamState.ofShore rotation shore root mark k hw,
    faceOfShore rotation shore root mark k hw)

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
end Mettapedia.GraphTheory.FourColor.CofacialSeamState
