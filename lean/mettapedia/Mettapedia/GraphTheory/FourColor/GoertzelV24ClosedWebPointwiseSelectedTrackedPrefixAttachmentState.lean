import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFiniteColorCompatibility
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState

/-!
# Pointwise-selected tracked prefix attachments

The selected Cell and seam have a fixed carrier of at most twenty-one edges,
but a cumulative prefix can connect two represented edges by leaving that
carrier and returning.  This module contracts the complete terminal-aware
prefix into the same finite supported-port residual state used by the rooted
Cell machine.

The construction is colour-parametric.  Together with the complete selected
terminal profile it recovers literal tracked reachability exactly on every
represented carrier edge, without the historical global shared-edge receipt.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24CorridorProfile
open GoertzelV24FramedTrail
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24SimpleGraphPortResidualFactorContraction
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace Formation

/-- Exact finite predecessor attachment state of an arbitrary colour function
on the selected terminal-aware cumulative prefix. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) :
    SourceLocalLayerSerialTrackedPrefixAttachmentState :=
  let inputData :=
    pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt
      formation corridor hinterior offset
  let edgeAt := fun edge : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset} => edge.1
  fun pair =>
    padSupportedPortResidualCode
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionEdgeAtSlot?
        formation corridor hinterior offset)
      (exactSupportedPortResidualCode
        (regionalTrackedEdgeGraph formation.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
            formation corridor hinterior offset)
          color (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2)
        edgeAt inputData.portEdge)

/-- The complete selected terminal profile is exact for connectivity between
its two incoming ports and retained terminal rung. -/
private theorem pointwiseSelectedTerminalInputProfileForColorAt_portConnected_exact
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation
        corridor hinterior offset step) ≠ 0)
    (pair : TrackedColorPair) :
    let inputData :=
      pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt
        formation corridor hinterior offset
    let graph := regionalTrackedEdgeGraph formation.annular.RS inputData.regionEdges
      color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
    let input :=
      pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt
        formation corridor hinterior offset color hcrossing
    (∀ left right,
      input.profile.strandConnected pair left right = true →
        graph.Reachable (inputData.portEdge left) (inputData.portEdge right)) ∧
    (∀ left right,
      inputData.portEdge left ∈ graph.support →
      inputData.portEdge right ∈ graph.support →
      graph.Reachable (inputData.portEdge left) (inputData.portEdge right) →
        input.profile.strandConnected pair left right = true) := by
  dsimp only
  let inputData :=
    pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt
      formation corridor hinterior offset
  let graph := regionalTrackedEdgeGraph formation.annular.RS inputData.regionEdges
    color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let input :=
    pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt
      formation corridor hinterior offset color hcrossing
  constructor
  · intro left right hconnected
    exact
      (inputData.regionalProfile_strandConnected_eq_true_iff color hcrossing
        pair left right).1 hconnected |>.2.2.2.2
  · intro left right hleftSupport hrightSupport hreachable
    rcases (SimpleGraph.mem_support graph).1 hleftSupport with
      ⟨leftNeighbor, hleftAdj⟩
    rcases (SimpleGraph.mem_support graph).1 hrightSupport with
      ⟨rightNeighbor, hrightAdj⟩
    exact
      (inputData.regionalProfile_strandConnected_eq_true_iff color hcrossing
        pair left right).2
        ⟨pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt_portsInRegion
            formation corridor hinterior offset left,
          pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt_portsInRegion
            formation corridor hinterior offset right,
          hleftAdj.1.2.1, hrightAdj.1.2.1, hreachable⟩

/-- The selected finite attachment state and complete terminal profile recover
literal cumulative-prefix reachability on every represented transition edge.
This is both soundness and completeness of the tracked predecessor summary. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt_factoredReachability_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset).card ≤ 6)
    (color : G.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation
        corridor hinterior offset step) ≠ 0)
    (pair : TrackedColorPair)
    (left right : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset}) :
    sourceLocalLayerSerialTrackedPrefixFactoredReachability
        (pointwiseSelectedSourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt
          formation corridor hinterior offset color)
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt
          formation corridor hinterior offset color hcrossing)
        pair
        (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt formation
          corridor hinterior offset hcell left)
        (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt formation
          corridor hinterior offset hcell right) ↔
      (regionalTrackedEdgeGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          formation corridor hinterior offset)
        color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable left.1 right.1 := by
  let inputData :=
    pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt
      formation corridor hinterior offset
  let graph := regionalTrackedEdgeGraph formation.annular.RS inputData.regionEdges
    color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let edgeAt := fun edge : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset} => edge.1
  let input :=
    pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt
      formation corridor hinterior offset color hcrossing
  let portConnected := fun leftPort rightPort : CorridorPort 2 1 =>
    input.profile.strandConnected pair leftPort rightPort = true
  have hports :=
    pointwiseSelectedTerminalInputProfileForColorAt_portConnected_exact formation
      corridor hinterior offset color hcrossing pair
  have hexact :
      graph.Reachable (edgeAt left) (edgeAt right) ↔
        SupportedPortResidualFactoredReachability
          (exactSupportedPortResidualCode graph edgeAt inputData.portEdge)
          portConnected left right := by
    exact reachable_iff_exactSupportedPortResidualFactoredReachability graph
      edgeAt inputData.portEdge portConnected hports.1 hports.2 left right
  change SupportedPortResidualFactoredReachability
      (padSupportedPortResidualCode
        (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionEdgeAtSlot?
          formation corridor hinterior offset)
        (exactSupportedPortResidualCode graph edgeAt inputData.portEdge))
      portConnected
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt formation
        corridor hinterior offset hcell left)
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt formation
        corridor hinterior offset hcell right) ↔ _
  simp only [SupportedPortResidualFactoredReachability,
    PortResidualFactoredReachability, padSupportedPortResidualCode,
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionEdgeAtSlot?_slot]
  exact hexact.symm

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
