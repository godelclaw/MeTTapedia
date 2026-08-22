import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileSeamResidual

/-!
# Refining a residual seam across a union

If a right-hand region is adjoined in two stages, a residual turn from the
old region into their union already occurs at one of the two staged seams.
This is a set-theoretic fact about the exact residual definitions.  It lets a
serial transition reuse its boundary-rebase and one-Cell seam codes instead
of introducing a third independent residual object.

Both tracked edge connectivity and occurrence-sensitive facial continuation
are covered.  No finiteness, determinism, or corridor geometry is assumed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TerminalProfileSeamUnion

open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24HexFaceRungType
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A residual tracked turn from `left` into `middle ∪ right` already
belongs either to the first seam `left | middle` or to the second seam
`(left ∪ middle) | right`. -/
theorem regionalTrackedSeamGraph_left_union_le
    (RS : RotationSystem V E) (left middle right : Finset E)
    (C : E → Color) (a b : Color) :
    regionalTrackedSeamGraph RS left (middle ∪ right) C a b ≤
      regionalTrackedSeamGraph RS left middle C a b ⊔
        regionalTrackedSeamGraph RS (left ∪ middle) right C a b := by
  intro x y hxy
  have hraw := (regionalTrackedSeamGraph_adj_iff RS left (middle ∪ right)
    C a b x y).1 hxy
  rcases hraw with ⟨htracked, hforward | hbackward⟩
  · rcases Finset.mem_union.1 hforward.2.2.1 with hyMiddle | hyRight
    · apply (SimpleGraph.sup_adj _ _ _ _).2
      exact Or.inl ((regionalTrackedSeamGraph_adj_iff RS left middle C a b
        x y).2 ⟨htracked, Or.inl
          ⟨hforward.1, fun hxMiddle => hforward.2.1
            (Finset.mem_union_left _ hxMiddle), hyMiddle,
            hforward.2.2.2⟩⟩)
    · by_cases hyMiddle : y ∈ middle
      · apply (SimpleGraph.sup_adj _ _ _ _).2
        exact Or.inl ((regionalTrackedSeamGraph_adj_iff RS left middle C a b
          x y).2 ⟨htracked, Or.inl
            ⟨hforward.1, fun hxMiddle => hforward.2.1
              (Finset.mem_union_left _ hxMiddle), hyMiddle,
              hforward.2.2.2⟩⟩)
      · apply (SimpleGraph.sup_adj _ _ _ _).2
        exact Or.inr ((regionalTrackedSeamGraph_adj_iff RS
          (left ∪ middle) right C a b x y).2 ⟨htracked, Or.inl
            ⟨Finset.mem_union_left _ hforward.1,
              fun hxRight => hforward.2.1
                (Finset.mem_union_right _ hxRight),
              hyRight, fun hyLeftMiddle => by
                rcases Finset.mem_union.1 hyLeftMiddle with hyLeft | hyMiddle'
                · exact hforward.2.2.2 hyLeft
                · exact hyMiddle hyMiddle'⟩⟩)
  · rcases Finset.mem_union.1 hbackward.1 with hxMiddle | hxRight
    · apply (SimpleGraph.sup_adj _ _ _ _).2
      exact Or.inl ((regionalTrackedSeamGraph_adj_iff RS left middle C a b
        x y).2 ⟨htracked, Or.inr
          ⟨hxMiddle, hbackward.2.1, hbackward.2.2.1,
            fun hyMiddle => hbackward.2.2.2
              (Finset.mem_union_left _ hyMiddle)⟩⟩)
    · by_cases hxMiddle : x ∈ middle
      · apply (SimpleGraph.sup_adj _ _ _ _).2
        exact Or.inl ((regionalTrackedSeamGraph_adj_iff RS left middle C a b
          x y).2 ⟨htracked, Or.inr
            ⟨hxMiddle, hbackward.2.1, hbackward.2.2.1,
              fun hyMiddle => hbackward.2.2.2
                (Finset.mem_union_left _ hyMiddle)⟩⟩)
      · apply (SimpleGraph.sup_adj _ _ _ _).2
        exact Or.inr ((regionalTrackedSeamGraph_adj_iff RS
          (left ∪ middle) right C a b x y).2 ⟨htracked, Or.inr
            ⟨hxRight, fun hxLeftMiddle => by
                rcases Finset.mem_union.1 hxLeftMiddle with hxLeft | hxMiddle'
                · exact hbackward.2.1 hxLeft
                · exact hxMiddle hxMiddle',
              Finset.mem_union_left _ hbackward.2.2.1,
              fun hyRight => hbackward.2.2.2
                (Finset.mem_union_right _ hyRight)⟩⟩)

/-- The same staged-seam refinement for cyclic face positions. -/
theorem faceRegionalSeamGraph_left_union_le
    (RS : RotationSystem V E) (root : RS.D)
    (left middle right : Finset E) :
    faceRegionalSeamGraph RS root left (middle ∪ right) ≤
      faceRegionalSeamGraph RS root left middle ⊔
        faceRegionalSeamGraph RS root (left ∪ middle) right := by
  intro x y hxy
  have hraw := (faceRegionalSeamGraph_adj_iff RS root left (middle ∪ right)
    x y).1 hxy
  rcases hraw with ⟨hface, hforward | hbackward⟩
  · rcases Finset.mem_union.1 hforward.2.2.1 with hyMiddle | hyRight
    · apply (SimpleGraph.sup_adj _ _ _ _).2
      exact Or.inl ((faceRegionalSeamGraph_adj_iff RS root left middle x y).2
        ⟨hface, Or.inl ⟨hforward.1, fun hxMiddle => hforward.2.1
          (Finset.mem_union_left _ hxMiddle), hyMiddle,
          hforward.2.2.2⟩⟩)
    · by_cases hyMiddle : faceCycleEdge RS root y ∈ middle
      · apply (SimpleGraph.sup_adj _ _ _ _).2
        exact Or.inl ((faceRegionalSeamGraph_adj_iff RS root left middle x y).2
          ⟨hface, Or.inl ⟨hforward.1, fun hxMiddle => hforward.2.1
            (Finset.mem_union_left _ hxMiddle), hyMiddle,
            hforward.2.2.2⟩⟩)
      · apply (SimpleGraph.sup_adj _ _ _ _).2
        exact Or.inr ((faceRegionalSeamGraph_adj_iff RS root
          (left ∪ middle) right x y).2 ⟨hface, Or.inl
            ⟨Finset.mem_union_left _ hforward.1,
              fun hxRight => hforward.2.1
                (Finset.mem_union_right _ hxRight),
              hyRight, fun hyLeftMiddle => by
                rcases Finset.mem_union.1 hyLeftMiddle with hyLeft | hyMiddle'
                · exact hforward.2.2.2 hyLeft
                · exact hyMiddle hyMiddle'⟩⟩)
  · rcases Finset.mem_union.1 hbackward.1 with hxMiddle | hxRight
    · apply (SimpleGraph.sup_adj _ _ _ _).2
      exact Or.inl ((faceRegionalSeamGraph_adj_iff RS root left middle x y).2
        ⟨hface, Or.inr ⟨hxMiddle, hbackward.2.1, hbackward.2.2.1,
          fun hyMiddle => hbackward.2.2.2
            (Finset.mem_union_left _ hyMiddle)⟩⟩)
    · by_cases hxMiddle : faceCycleEdge RS root x ∈ middle
      · apply (SimpleGraph.sup_adj _ _ _ _).2
        exact Or.inl ((faceRegionalSeamGraph_adj_iff RS root left middle x y).2
          ⟨hface, Or.inr ⟨hxMiddle, hbackward.2.1, hbackward.2.2.1,
            fun hyMiddle => hbackward.2.2.2
              (Finset.mem_union_left _ hyMiddle)⟩⟩)
      · apply (SimpleGraph.sup_adj _ _ _ _).2
        exact Or.inr ((faceRegionalSeamGraph_adj_iff RS root
          (left ∪ middle) right x y).2 ⟨hface, Or.inr
            ⟨hxRight, fun hxLeftMiddle => by
                rcases Finset.mem_union.1 hxLeftMiddle with hxLeft | hxMiddle'
                · exact hbackward.2.1 hxLeft
                · exact hxMiddle hxMiddle',
              Finset.mem_union_left _ hbackward.2.2.1,
              fun hyRight => hbackward.2.2.2
                (Finset.mem_union_right _ hyRight)⟩⟩)

end

end GoertzelV24TerminalProfileSeamUnion

end Mettapedia.GraphTheory.FourColor
