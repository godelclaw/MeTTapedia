import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAssemblyAppend

/-!
# L1: compatibility of consecutive selected-rail successor frames

Successor frames are constructed independently at consecutive seams.  Their
shared Cell-3 placement nevertheless chooses the same two outgoing flank
slots: on a six-cycle the slot immediately before, and respectively after,
the outgoing rung is unique.  Consequently the separated right-cell rails
stored by one successor can be reused as the left-cell rails for the next.

This is coordinate compatibility, not an arbitrary-length assembly.  It does
not prove existence of a successor at every seam, global support separation,
either annular end cap, or Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 <
      blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {middlePlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior (nextCorridorInterior leftInterior hnext) hnextNext)}

private theorem selectedSidePosition_eq_of_successor_mod
    (placement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext))
    (first second :
      {position // position ∈ selectedPlacementSidePositions placement})
    (hfirst : placement.outgoingPosition.val ≡ first.1.val + 1 [MOD 6])
    (hsecond : placement.outgoingPosition.val ≡ second.1.val + 1 [MOD 6]) :
    first = second := by
  apply Subtype.ext
  apply Fin.ext
  simp only [Nat.ModEq] at hfirst hsecond
  have hfirstBound : first.1.val < 6 := by
    simpa only [placement.orbit_card] using first.1.isLt
  have hsecondBound : second.1.val < 6 := by
    simpa only [placement.orbit_card] using second.1.isLt
  omega

private theorem selectedSidePosition_eq_of_predecessor_mod
    (placement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext))
    (first second :
      {position // position ∈ selectedPlacementSidePositions placement})
    (hfirst : first.1.val ≡ placement.outgoingPosition.val + 1 [MOD 6])
    (hsecond : second.1.val ≡ placement.outgoingPosition.val + 1 [MOD 6]) :
    first = second := by
  apply Subtype.ext
  apply Fin.ext
  simp only [Nat.ModEq] at hfirst hsecond
  have hfirstBound : first.1.val < 6 := by
    simpa only [placement.orbit_card] using first.1.isLt
  have hsecondBound : second.1.val < 6 := by
    simpa only [placement.orbit_card] using second.1.isLt
  omega

/-- Independently constructed successor frames choose the same slot before
the shared placement's outgoing rung. -/
theorem SeparatedSelectedSourceLocalRailSuccessor.rightOutgoingBefore_eq_nextLeftBefore
    (first : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      middlePlacement)
    (second : SeparatedSelectedSourceLocalRailSuccessor hnextNext middlePlacement
      rightPlacement) :
    first.rightOutgoingBefore = second.frame.leftBefore := by
  exact selectedSidePosition_eq_of_successor_mod middlePlacement
    first.rightOutgoingBefore second.frame.leftBefore
      first.rightOutgoingBefore_mod second.frame.leftBefore_mod

/-- Independently constructed successor frames choose the same slot after
the shared placement's outgoing rung. -/
theorem SeparatedSelectedSourceLocalRailSuccessor.rightOutgoingAfter_eq_nextLeftAfter
    (first : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      middlePlacement)
    (second : SeparatedSelectedSourceLocalRailSuccessor hnextNext middlePlacement
      rightPlacement) :
    first.rightOutgoingAfter = second.frame.leftAfter := by
  exact selectedSidePosition_eq_of_predecessor_mod middlePlacement
    first.rightOutgoingAfter second.frame.leftAfter
      first.rightOutgoingAfter_mod second.frame.leftAfter_mod

/-- The separated rails selected in the right cell of one seam are exactly a
valid left-cell rail pair for the next seam. -/
noncomputable def SeparatedSelectedSourceLocalRailSuccessor.rightRailsAsNextLeft
    (first : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      middlePlacement)
    (second : SeparatedSelectedSourceLocalRailSuccessor hnextNext middlePlacement
      rightPlacement) :
    SeparatedSelectedSourceLocalRailPaths middlePlacement
      first.frame.rightAfter first.frame.rightBefore second.frame.leftBefore
      second.frame.leftAfter := by
  rw [← first.rightOutgoingBefore_eq_nextLeftBefore second,
    ← first.rightOutgoingAfter_eq_nextLeftAfter second]
  exact first.rightRails

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
