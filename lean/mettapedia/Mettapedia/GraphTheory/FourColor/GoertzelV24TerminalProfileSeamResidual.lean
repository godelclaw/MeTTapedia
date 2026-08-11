import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphSupResidual
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileRegionalCoverage

/-!
# Exact seam terms in a one-Cell profile update

The old-prefix and Cell graphs need not cover every adjacency of their union:
an edge retained only by the prefix can be adjacent to one retained only by
the Cell.  The exact update therefore has a canonical third factor, the
residual seam graph.  The earlier two-factor coverage theorems are precisely
the special case in which this residual is empty.

Both tracked connectivity and occurrence-sensitive face progress are treated
in the same form.  No determinism or concrete corridor coverage is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TerminalProfileSeamResidual

open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24HexFaceRungType
open GoertzelV24RotationFaceFragments
open GoertzelV24SimpleGraphSupResidual
open GoertzelV24TerminalProfileConnectivityUpdate
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The tracked adjacencies present in the enlarged region but in neither
regional factor separately. -/
def regionalTrackedSeamGraph
    (RS : RotationSystem V E) (leftRegion rightRegion : Finset E)
    (C : E → Color) (a b : Color) : SimpleGraph E :=
  supResidual
    (regionalTrackedEdgeGraph RS (leftRegion ∪ rightRegion) C a b)
    (regionalTrackedEdgeGraph RS leftRegion C a b)
    (regionalTrackedEdgeGraph RS rightRegion C a b)

/-- A residual tracked edge is exactly a tracked adjacency crossing from the
left-only part to the right-only part, in either orientation. -/
theorem regionalTrackedSeamGraph_adj_iff
    (RS : RotationSystem V E) (leftRegion rightRegion : Finset E)
    (C : E → Color) (a b : Color) (x y : E) :
    (regionalTrackedSeamGraph RS leftRegion rightRegion C a b).Adj x y ↔
      (RS.trackedEdgeGraph C a b).Adj x y ∧
        ((x ∈ leftRegion ∧ x ∉ rightRegion ∧
            y ∈ rightRegion ∧ y ∉ leftRegion) ∨
          (x ∈ rightRegion ∧ x ∉ leftRegion ∧
            y ∈ leftRegion ∧ y ∉ rightRegion)) := by
  constructor
  · rintro ⟨⟨hadj, hx, hy⟩, hnotLeft, hnotRight⟩
    simp only [Finset.mem_union] at hx hy
    rcases hx with hxLeft | hxRight <;> rcases hy with hyLeft | hyRight
    · exact (hnotLeft ⟨hadj, hxLeft, hyLeft⟩).elim
    · exact ⟨hadj, Or.inl ⟨hxLeft,
        fun hxRight => hnotRight ⟨hadj, hxRight, hyRight⟩,
        hyRight, fun hyLeft => hnotLeft ⟨hadj, hxLeft, hyLeft⟩⟩⟩
    · exact ⟨hadj, Or.inr ⟨hxRight,
        fun hxLeft => hnotLeft ⟨hadj, hxLeft, hyLeft⟩,
        hyLeft, fun hyRight => hnotRight ⟨hadj, hxRight, hyRight⟩⟩⟩
    · exact (hnotRight ⟨hadj, hxRight, hyRight⟩).elim
  · rintro ⟨hadj, hcross | hcross⟩
    · exact ⟨
        ⟨hadj, Finset.mem_union_left _ hcross.1,
          Finset.mem_union_right _ hcross.2.2.1⟩,
        (fun hleft => hcross.2.2.2 hleft.2.2),
        (fun hright => hcross.2.1 hright.2.1)⟩
    · exact ⟨
        ⟨hadj, Finset.mem_union_right _ hcross.1,
          Finset.mem_union_left _ hcross.2.2.1⟩,
        (fun hleft => hcross.2.1 hleft.2.1),
        (fun hright => hcross.2.2.2 hright.2.2)⟩

/-- Prefix, Cell, and the explicit seam residual recover the enlarged
tracked graph exactly, without a coverage hypothesis. -/
theorem regionalTrackedEdgeGraph_union_eq_sup_sup_seam
    (RS : RotationSystem V E) (leftRegion rightRegion : Finset E)
    (C : E → Color) (a b : Color) :
    regionalTrackedEdgeGraph RS (leftRegion ∪ rightRegion) C a b =
      (regionalTrackedEdgeGraph RS leftRegion C a b ⊔
        regionalTrackedEdgeGraph RS rightRegion C a b) ⊔
          regionalTrackedSeamGraph RS leftRegion rightRegion C a b := by
  symm
  exact sup_sup_supResidual_eq _ _ _
    (regionalTrackedEdgeGraph_mono RS C a b Finset.subset_union_left)
    (regionalTrackedEdgeGraph_mono RS C a b Finset.subset_union_right)

/-- The old tracked-coverage premise says exactly that the newly exposed seam
factor is empty. -/
theorem regionalTrackedAdjacencyCovered_iff_seam_eq_bot
    (RS : RotationSystem V E) (leftRegion rightRegion : Finset E)
    (C : E → Color) (a b : Color) :
    RegionalTrackedAdjacencyCovered RS leftRegion rightRegion C a b ↔
      regionalTrackedSeamGraph RS leftRegion rightRegion C a b = ⊥ := by
  rw [regionalTrackedSeamGraph, supResidual_eq_bot_iff]
  constructor
  · intro hcovered x y hxy
    rcases hcovered hxy.1 hxy.2.1 hxy.2.2 with hleft | hright
    · exact Or.inl ⟨hxy.1, hleft⟩
    · exact Or.inr ⟨hxy.1, hright⟩
  · intro hcovered x y hadj hx hy
    have hxy : (regionalTrackedEdgeGraph RS
        (leftRegion ∪ rightRegion) C a b).Adj x y := ⟨hadj, hx, hy⟩
    rcases hcovered hxy with hleft | hright
    · exact Or.inl ⟨hleft.2.1, hleft.2.2⟩
    · exact Or.inr ⟨hright.2.1, hright.2.2⟩

/-- The face-cycle adjacencies present in the enlarged region but in neither
regional factor separately.  Its vertices remain actual face occurrences. -/
def faceRegionalSeamGraph
    (RS : RotationSystem V E) (root : RS.D)
    (leftRegion rightRegion : Finset E) :
    SimpleGraph (Fin (RS.faceOrbit root).card) :=
  supResidual
    (faceRegionalAmbientPositionGraph RS root (leftRegion ∪ rightRegion))
    (faceRegionalAmbientPositionGraph RS root leftRegion)
    (faceRegionalAmbientPositionGraph RS root rightRegion)

/-- A residual facial step is exactly a face-cycle adjacency crossing between
the two exclusive regional parts. -/
theorem faceRegionalSeamGraph_adj_iff
    (RS : RotationSystem V E) (root : RS.D)
    (leftRegion rightRegion : Finset E)
    (x y : Fin (RS.faceOrbit root).card) :
    (faceRegionalSeamGraph RS root leftRegion rightRegion).Adj x y ↔
      (faceCyclePositionGraph RS root).Adj x y ∧
        ((faceCycleEdge RS root x ∈ leftRegion ∧
            faceCycleEdge RS root x ∉ rightRegion ∧
            faceCycleEdge RS root y ∈ rightRegion ∧
            faceCycleEdge RS root y ∉ leftRegion) ∨
          (faceCycleEdge RS root x ∈ rightRegion ∧
            faceCycleEdge RS root x ∉ leftRegion ∧
            faceCycleEdge RS root y ∈ leftRegion ∧
            faceCycleEdge RS root y ∉ rightRegion)) := by
  constructor
  · rintro ⟨⟨hadj, hx, hy⟩, hnotLeft, hnotRight⟩
    simp only [Finset.mem_union] at hx hy
    rcases hx with hxLeft | hxRight <;> rcases hy with hyLeft | hyRight
    · exact (hnotLeft ⟨hadj, hxLeft, hyLeft⟩).elim
    · exact ⟨hadj, Or.inl ⟨hxLeft,
        fun hxRight => hnotRight ⟨hadj, hxRight, hyRight⟩,
        hyRight, fun hyLeft => hnotLeft ⟨hadj, hxLeft, hyLeft⟩⟩⟩
    · exact ⟨hadj, Or.inr ⟨hxRight,
        fun hxLeft => hnotLeft ⟨hadj, hxLeft, hyLeft⟩,
        hyLeft, fun hyRight => hnotRight ⟨hadj, hxRight, hyRight⟩⟩⟩
    · exact (hnotRight ⟨hadj, hxRight, hyRight⟩).elim
  · rintro ⟨hadj, hcross | hcross⟩
    · exact ⟨
        ⟨hadj, Finset.mem_union_left _ hcross.1,
          Finset.mem_union_right _ hcross.2.2.1⟩,
        (fun hleft => hcross.2.2.2 hleft.2.2),
        (fun hright => hcross.2.1 hright.2.1)⟩
    · exact ⟨
        ⟨hadj, Finset.mem_union_right _ hcross.1,
          Finset.mem_union_left _ hcross.2.2.1⟩,
        (fun hleft => hcross.2.1 hleft.2.1),
        (fun hright => hcross.2.2.2 hright.2.2)⟩

/-- Prefix, Cell, and the explicit seam residual recover the enlarged
occurrence-sensitive face graph exactly. -/
theorem faceRegionalAmbientPositionGraph_union_eq_sup_sup_seam
    (RS : RotationSystem V E) (root : RS.D)
    (leftRegion rightRegion : Finset E) :
    faceRegionalAmbientPositionGraph RS root (leftRegion ∪ rightRegion) =
      (faceRegionalAmbientPositionGraph RS root leftRegion ⊔
        faceRegionalAmbientPositionGraph RS root rightRegion) ⊔
          faceRegionalSeamGraph RS root leftRegion rightRegion := by
  have hleft : faceRegionalAmbientPositionGraph RS root leftRegion ≤
      faceRegionalAmbientPositionGraph RS root
        (leftRegion ∪ rightRegion) := by
    intro x y hxy
    exact ⟨hxy.1, Finset.mem_union_left _ hxy.2.1,
      Finset.mem_union_left _ hxy.2.2⟩
  have hright : faceRegionalAmbientPositionGraph RS root rightRegion ≤
      faceRegionalAmbientPositionGraph RS root
        (leftRegion ∪ rightRegion) := by
    intro x y hxy
    exact ⟨hxy.1, Finset.mem_union_right _ hxy.2.1,
      Finset.mem_union_right _ hxy.2.2⟩
  symm
  exact sup_sup_supResidual_eq _ _ _ hleft hright

/-- The old facial-coverage premise is exactly the zero-residual special
case of the exact three-factor update. -/
theorem regionalFaceAdjacencyCovered_iff_seam_eq_bot
    (RS : RotationSystem V E) (root : RS.D)
    (leftRegion rightRegion : Finset E) :
    RegionalFaceAdjacencyCovered RS root leftRegion rightRegion ↔
      faceRegionalSeamGraph RS root leftRegion rightRegion = ⊥ := by
  rw [faceRegionalSeamGraph, supResidual_eq_bot_iff]
  constructor
  · intro hcovered x y hxy
    rcases hcovered hxy.1 hxy.2.1 hxy.2.2 with hleft | hright
    · exact Or.inl ⟨hxy.1, hleft⟩
    · exact Or.inr ⟨hxy.1, hright⟩
  · intro hcovered x y hadj hx hy
    have hxy : (faceRegionalAmbientPositionGraph RS root
        (leftRegion ∪ rightRegion)).Adj x y := ⟨hadj, hx, hy⟩
    rcases hcovered hxy with hleft | hright
    · exact Or.inl ⟨hleft.2.1, hleft.2.2⟩
    · exact Or.inr ⟨hright.2.1, hright.2.2⟩

end

end GoertzelV24TerminalProfileSeamResidual

end Mettapedia.GraphTheory.FourColor
