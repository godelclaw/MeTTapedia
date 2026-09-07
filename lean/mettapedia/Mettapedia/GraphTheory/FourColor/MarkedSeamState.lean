import Mettapedia.GraphTheory.FourColor.GoertzelV24MajorityShorePhysicalReplacement
import Mettapedia.GraphTheory.FourColor.GoertzelV24NormalizedShoreDescent

/-!
# Finite seam states retaining named ambient darts

The seam-and-support state does not name persistent edges.  An optional
coordinate for each designated dart supplies exactly that missing datum.
Equality of these coordinates forces the existing physical replacement
matching to use the original ambient partner on every designated crossing.
The finite cost depends on the number of designated darts, not on the
ambient graph size. No colouring enumeration is performed here.
-/

namespace Mettapedia.GraphTheory.FourColor.MarkedSeamState

open GoertzelV24NormalizedSeamState GoertzelV24NormalizedTaitSupport
open GoertzelV24NormalizedShoreDescent GoertzelV24MajorityShoreNormalizedState
open GoertzelV24MajorityShorePhysicalReplacement
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24VertexSideReassembly GoertzelV24VertexSideOpenTangle

noncomputable section
universe u v
attribute [local instance] Classical.propDecidable

variable {M : Type v}

/-- A full exact state and positions of a fixed family of named darts. -/
abbrev Marked (M : Type v) (k : ℕ) :=
  State.{u} k × (M → Option (StandardPort.{u} k))

theorem card_marked [Fintype M] (k : ℕ) :
    Fintype.card (Marked.{u} M k) =
      (Nat.factorial k * 2 ^ (3 ^ k)) * (k + 1) ^ Fintype.card M := by
  simp [Marked, Fintype.card_prod, card_state, StandardPort]

/-- Width is part of the finite state; no equality of widths is assumed. -/
abbrev Bounded (M : Type v) (k : ℕ) :=
  Σ j : Fin (k + 1), Marked.{u} M j.val

/-- A computable upper bound using at most `t` named darts. -/
def stateBound (k t : ℕ) : ℕ :=
  (∑ j : Fin (k + 1), Nat.factorial j.val * 2 ^ (3 ^ j.val)) * (k + 1) ^ t

theorem card_bounded_le [Fintype M] (k : ℕ) :
    Fintype.card (Bounded.{u} M k) ≤ stateBound k (Fintype.card M) := by
  rw [Fintype.card_sigma]
  simp only [card_marked]
  unfold stateBound
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show j.val + 1 ≤ k + 1 by omega) _)

variable {V E : Type u} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- The optional coordinate is absent exactly when the named dart is not
on this complete boundary. -/
def positions (RS : RotationSystem V E) (side : V → Prop) (k : ℕ)
    (coordinate : BoundaryDart RS side ≃ StandardPort.{u} k)
    (mark : M → RS.D) (m : M) : Option (StandardPort.{u} k) :=
  if h : side (RS.vertOf (mark m)) ∧ ¬ side (RS.vertOf (RS.alpha (mark m))) then
    some (coordinate ⟨⟨mark m, h.1⟩, h.2⟩) else none

theorem positions_boundary (RS : RotationSystem V E) (side : V → Prop) (k : ℕ)
    (coordinate : BoundaryDart RS side ≃ StandardPort.{u} k)
    (mark : M → RS.D) (m : M) (b : BoundaryDart RS side)
    (hb : b.val.val = mark m) :
    positions RS side k coordinate mark m = some (coordinate b) := by
  unfold positions
  simp [← hb, b.val.property, b.property]

/-- Equality of optional coordinates fixes the actual named dart, not just
its rank among the marked subset. It also derives membership on the new side. -/
theorem matching_fixes_mark (RS : RotationSystem V E) (oldSide newSide : V → Prop)
    (k : ℕ) (oldCoordinate : BoundaryDart RS oldSide ≃ StandardPort.{u} k)
    (newCoordinate : BoundaryDart RS newSide ≃ StandardPort.{u} k)
    (mark : M → RS.D)
    (hpos : positions RS oldSide k oldCoordinate mark =
      positions RS newSide k newCoordinate mark)
    (b : BoundaryDart RS oldSide) (m : M) (hb : b.val.val = mark m) :
    ((oldCoordinate.trans newCoordinate.symm) b).val.val = mark m := by
  have heq := congrFun hpos m
  rw [positions_boundary RS oldSide k oldCoordinate mark m b hb] at heq
  unfold positions at heq
  split_ifs at heq with h
  · have hc := Option.some.inj heq
    have hd := congrArg newCoordinate.symm hc
    simpa using congrArg (fun d : BoundaryDart RS newSide => d.val.val) hd

section GraphBacked
variable {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- The old exact state augmented by the positions of the named darts. -/
def ofShore (rotation : SimpleGraphDartRotation.Data G) (shore : Finset G.edgeSet)
    (root : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (mark : M → G.Dart) (k : ℕ) (hwidth : boundaryWidth rotation shore = k) :
    Marked.{u} M k :=
  (normalizedState rotation shore root k hwidth,
    positions rotation.toRotationSystem (majorityRetainedKeep G shore) k
      (boundaryCoordinate rotation shore k hwidth) mark)

def boundedOfShore (rotation : SimpleGraphDartRotation.Data G) (shore : Finset G.edgeSet)
    (root : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (mark : M → G.Dart) (k : ℕ) (hbound : boundaryWidth rotation shore ≤ k) :
    Bounded.{u} M k :=
  ⟨⟨boundaryWidth rotation shore, by omega⟩,
    ofShore rotation shore root mark _ rfl⟩

omit [G.LocallyFinite] in
theorem ofShore_ndrec (rotation : SimpleGraphDartRotation.Data G)
    (shore : Finset G.edgeSet)
    (root : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (mark : M → G.Dart) (width : ℕ) (hw : boundaryWidth rotation shore = width) :
    Eq.ndrec (ofShore rotation shore root mark _ rfl) hw =
      ofShore rotation shore root mark width hw := by
  cases hw
  rfl

omit [G.LocallyFinite] in
/-- Equality in the varying-width carrier exposes a common width and the
joint equality of the exact state and named-dart coordinates. -/
theorem boundedOfShore_eq_elim (rotation : SimpleGraphDartRotation.Data G)
    (oldShore newShore : Finset G.edgeSet)
    (oldRoot : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G oldShore))
    (newRoot : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G newShore))
    (mark : M → G.Dart) (k : ℕ)
    (oldBound : boundaryWidth rotation oldShore ≤ k)
    (newBound : boundaryWidth rotation newShore ≤ k)
    (heq : boundedOfShore rotation oldShore oldRoot mark k oldBound =
      boundedOfShore rotation newShore newRoot mark k newBound) :
    ∃ width, ∃ oldWidth : boundaryWidth rotation oldShore = width,
      ∃ newWidth : boundaryWidth rotation newShore = width,
        ofShore rotation oldShore oldRoot mark width oldWidth =
          ofShore rotation newShore newRoot mark width newWidth := by
  rcases Sigma.ext_iff.mp heq with ⟨hi, hv⟩
  have hw : boundaryWidth rotation oldShore = boundaryWidth rotation newShore :=
    congrArg Fin.val hi
  refine ⟨boundaryWidth rotation newShore, hw, rfl, ?_⟩
  rw [← ofShore_ndrec rotation oldShore oldRoot mark _ hw]
  exact eq_of_heq ((eqRec_heq hw (ofShore rotation oldShore oldRoot mark _ rfl)).trans hv)

omit [G.LocallyFinite] in
/-- The physical replacement's seam retains ambient `alpha` on every named
old inner boundary dart. The matching is the existing constructor, unchanged. -/
theorem replacementMatching_mark (rotation : SimpleGraphDartRotation.Data G)
    (oldShore newShore : Finset G.edgeSet)
    (oldRoot : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G oldShore))
    (newRoot : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G newShore))
    (mark : M → G.Dart) (k : ℕ)
    (oldWidth : boundaryWidth rotation oldShore = k)
    (newWidth : boundaryWidth rotation newShore = k)
    (heq : ofShore rotation oldShore oldRoot mark k oldWidth =
      ofShore rotation newShore newRoot mark k newWidth)
    (b : BoundaryDart rotation.toRotationSystem (majorityDeletedKeep G oldShore))
    (m : M) (hb : rotation.toRotationSystem.alpha b.val.val = mark m) :
    (replacementMatching rotation oldShore newShore k oldWidth newWidth b).val.val =
      rotation.toRotationSystem.alpha b.val.val := by
  have hmark : (oldExteriorMatching rotation oldShore b).val.val = mark m := by
    rw [oldExteriorMatching, complementBoundaryAlphaEquiv_symm_val]
    exact hb
  exact (matching_fixes_mark rotation.toRotationSystem _ _ k
    (boundaryCoordinate rotation oldShore k oldWidth)
    (boundaryCoordinate rotation newShore k newWidth) mark
    (congrArg Prod.snd heq) (oldExteriorMatching rotation oldShore b) m hmark).trans hb.symm

omit [G.LocallyFinite] in
/-- The reverse orientation of a designated seam edge also retains its
ambient partner. Presence on the old boundary is derived from state equality. -/
theorem replacementMatching_symm_mark (rotation : SimpleGraphDartRotation.Data G)
    (oldShore newShore : Finset G.edgeSet)
    (oldRoot : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G oldShore))
    (newRoot : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G newShore))
    (mark : M → G.Dart) (k : ℕ)
    (oldWidth : boundaryWidth rotation oldShore = k)
    (newWidth : boundaryWidth rotation newShore = k)
    (heq : ofShore rotation oldShore oldRoot mark k oldWidth =
      ofShore rotation newShore newRoot mark k newWidth)
    (b : BoundaryDart rotation.toRotationSystem (majorityRetainedKeep G newShore))
    (m : M) (hb : b.val.val = mark m) :
    ((replacementMatching rotation oldShore newShore k oldWidth newWidth).symm b).val.val =
      rotation.toRotationSystem.alpha b.val.val := by
  have hd := matching_fixes_mark rotation.toRotationSystem _ _ k
    (boundaryCoordinate rotation newShore k newWidth)
    (boundaryCoordinate rotation oldShore k oldWidth) mark
    (congrArg Prod.snd heq.symm) b m hb
  change ((oldExteriorMatching rotation oldShore).symm
    (((boundaryCoordinate rotation newShore k newWidth).trans
      (boundaryCoordinate rotation oldShore k oldWidth).symm) b)).val.val = _
  rw [oldExteriorMatching]
  simp only [Equiv.symm_symm,
    GoertzelV24ComplementaryShoreBoundaryOrder.complementBoundaryAlphaEquiv_val]
  exact congrArg rotation.toRotationSystem.alpha (hd.trans hb.symm)

end GraphBacked
end
end Mettapedia.GraphTheory.FourColor.MarkedSeamState
