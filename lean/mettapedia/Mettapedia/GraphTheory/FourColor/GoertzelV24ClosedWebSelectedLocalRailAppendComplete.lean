import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendResidueCenterReroute

/-!
# L1: unconditional adjacent selected-rail append

The exact adjacent classifier previously returned six finite residual shapes.
Each is now constructive: four stationary-path/centre-bridge cases and two
centre-revisit shortcut cases.  This module packages those proofs into the
source-facing local result: two consecutive selected Cell-3 rail pairs always
assemble, with either the original or exchanged outgoing order.

The endpoint permutation is retained explicitly.  This is the complete local
append theorem, not yet a permutation-aware arbitrary-length fold, either
annular end cap, or closure of Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
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

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {leftIncomingBefore leftIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}

/-- The only two possible endpoint orders after a complete adjacent append. -/
inductive SelectedLocalRailAppendCompleteOutcome
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) : Type (u + 1)
  | straight
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace leftPlacement leftIncomingBefore)
        (selectedPlacementSideFace leftPlacement leftIncomingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter))
  | swapped
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace leftPlacement leftIncomingBefore)
        (selectedPlacementSideFace leftPlacement leftIncomingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore))

/-- **L1 complete adjacent append.** Literal selected rails in two consecutive
Cell-3 pieces always assemble as two simple support-disjoint paths.  The result
retains whether the outgoing labels are straight or exchanged. -/
noncomputable def appendLocalSuccessorComplete
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) :
    SelectedLocalRailAppendCompleteOutcome successor left := by
  cases classifyLocalSuccessorAppendLengthResolved successor left with
  | straight assembly => exact .straight assembly
  | swapped assembly => exact .swapped assembly
  | firstSecondSameFirst cross same lengths =>
      cases appendFirstSecondSameFirst cross same lengths with
      | inl assembly => exact .straight assembly
      | inr assembly => exact .swapped assembly
  | firstSecondSameSecond cross same lengths =>
      cases appendFirstSecondSameSecond cross same lengths with
      | inl assembly => exact .straight assembly
      | inr assembly => exact .swapped assembly
  | firstSecondCenter cross center lengths =>
      cases appendFirstSecondCenter cross center lengths with
      | inl assembly => exact .straight assembly
      | inr assembly => exact .swapped assembly
  | secondFirstSameFirst cross same lengths =>
      cases appendSecondFirstSameFirst cross same lengths with
      | inl assembly => exact .straight assembly
      | inr assembly => exact .swapped assembly
  | secondFirstSameSecond cross same lengths =>
      cases appendSecondFirstSameSecond cross same lengths with
      | inl assembly => exact .straight assembly
      | inr assembly => exact .swapped assembly
  | secondFirstCenter cross center lengths =>
      cases appendSecondFirstCenter cross center lengths with
      | inl assembly => exact .straight assembly
      | inr assembly => exact .swapped assembly

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
