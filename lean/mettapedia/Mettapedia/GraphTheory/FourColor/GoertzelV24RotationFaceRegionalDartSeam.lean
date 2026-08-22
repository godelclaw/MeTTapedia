import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationFaceRegionalDartGraph
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileSeamResidual

/-!
# Regional facial seams on literal darts

The occurrence-sensitive facial update is already available relative to one
chosen face root.  A finite serial recurrence also needs one root-independent
graph on literal darts, because predecessor fragments and local Cell
occurrences may initially be named from different roots of the same orbit.

This file defines the residual seam directly for `faceRegionalDartGraph` and
proves the exact union factorization.  It changes no profile semantics and
makes no two-sidedness assumption: the vertices remain literal dart
occurrences, so the two darts over a boundary-stub edge remain distinct.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationFaceRegionalDartSeam

open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24SimpleGraphSupResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Facial adjacencies present after adjoining the right region but present
in neither regional factor separately, on the literal dart carrier. -/
def faceRegionalDartSeamGraph
    (RS : RotationSystem V E) (leftRegion rightRegion : Finset E) :
    SimpleGraph RS.D :=
  supResidual
    (faceRegionalDartGraph RS (leftRegion ∪ rightRegion))
    (faceRegionalDartGraph RS leftRegion)
    (faceRegionalDartGraph RS rightRegion)

/-- A literal-dart seam edge is exactly a nontrivial face-permutation step
whose two underlying edges lie in opposite exclusive regional parts. -/
theorem faceRegionalDartSeamGraph_adj_iff
    (RS : RotationSystem V E) (leftRegion rightRegion : Finset E)
    (x y : RS.D) :
    (faceRegionalDartSeamGraph RS leftRegion rightRegion).Adj x y ↔
      x ≠ y ∧ (y = RS.phi x ∨ x = RS.phi y) ∧
        ((RS.edgeOf x ∈ leftRegion ∧ RS.edgeOf x ∉ rightRegion ∧
            RS.edgeOf y ∈ rightRegion ∧ RS.edgeOf y ∉ leftRegion) ∨
          (RS.edgeOf x ∈ rightRegion ∧ RS.edgeOf x ∉ leftRegion ∧
            RS.edgeOf y ∈ leftRegion ∧ RS.edgeOf y ∉ rightRegion)) := by
  constructor
  · rintro ⟨⟨hne, hstep, hx, hy⟩, hnotLeft, hnotRight⟩
    simp only [Finset.mem_union] at hx hy
    rcases hx with hxLeft | hxRight <;> rcases hy with hyLeft | hyRight
    · exact (hnotLeft ⟨hne, hstep, hxLeft, hyLeft⟩).elim
    · exact ⟨hne, hstep, Or.inl ⟨hxLeft,
        fun hxRight => hnotRight ⟨hne, hstep, hxRight, hyRight⟩,
        hyRight, fun hyLeft => hnotLeft ⟨hne, hstep, hxLeft, hyLeft⟩⟩⟩
    · exact ⟨hne, hstep, Or.inr ⟨hxRight,
        fun hxLeft => hnotLeft ⟨hne, hstep, hxLeft, hyLeft⟩,
        hyLeft, fun hyRight => hnotRight ⟨hne, hstep, hxRight, hyRight⟩⟩⟩
    · exact (hnotRight ⟨hne, hstep, hxRight, hyRight⟩).elim
  · rintro ⟨hne, hstep, hcross | hcross⟩
    · exact ⟨
        ⟨hne, hstep, Finset.mem_union_left _ hcross.1,
          Finset.mem_union_right _ hcross.2.2.1⟩,
        (fun hleft => hcross.2.2.2 hleft.2.2.2),
        (fun hright => hcross.2.1 hright.2.2.1)⟩
    · exact ⟨
        ⟨hne, hstep, Finset.mem_union_right _ hcross.1,
          Finset.mem_union_left _ hcross.2.2.1⟩,
        (fun hleft => hcross.2.1 hleft.2.2.1),
        (fun hright => hcross.2.2.2 hright.2.2.2)⟩

/-- Prefix, Cell, and the explicit literal-dart seam recover the enlarged
occurrence-sensitive face graph exactly. -/
theorem faceRegionalDartGraph_union_eq_sup_sup_seam
    (RS : RotationSystem V E) (leftRegion rightRegion : Finset E) :
    faceRegionalDartGraph RS (leftRegion ∪ rightRegion) =
      (faceRegionalDartGraph RS leftRegion ⊔
        faceRegionalDartGraph RS rightRegion) ⊔
          faceRegionalDartSeamGraph RS leftRegion rightRegion := by
  have hleft : faceRegionalDartGraph RS leftRegion ≤
      faceRegionalDartGraph RS (leftRegion ∪ rightRegion) := by
    intro x y hxy
    exact ⟨hxy.1, hxy.2.1,
      Finset.mem_union_left _ hxy.2.2.1,
      Finset.mem_union_left _ hxy.2.2.2⟩
  have hright : faceRegionalDartGraph RS rightRegion ≤
      faceRegionalDartGraph RS (leftRegion ∪ rightRegion) := by
    intro x y hxy
    exact ⟨hxy.1, hxy.2.1,
      Finset.mem_union_right _ hxy.2.2.1,
      Finset.mem_union_right _ hxy.2.2.2⟩
  symm
  exact sup_sup_supResidual_eq _ _ _ hleft hright

end

end GoertzelV24RotationFaceRegionalDartSeam

end Mettapedia.GraphTheory.FourColor
