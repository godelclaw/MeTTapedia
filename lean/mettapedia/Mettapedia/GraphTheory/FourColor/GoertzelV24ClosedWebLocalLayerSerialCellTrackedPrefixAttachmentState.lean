import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableTrackedState

/-!
# Finite prefix attachments on the source-Cell transition carrier

The literal Cell and its residual seam now share one carrier of at most
twenty-one edges.  The accumulated prefix can nevertheless connect two of
those edges by leaving that carrier and returning, so its contribution may
not be replaced by the induced local graph.

This file records exactly the missing predecessor information.  For each
tracked colour pair, every one of the twenty-one stable slots records whether
it meets one of the three incoming profile ports (two crossings and the shared
rung) or belongs to a port-free residual component.  The code is extracted
from the actual cumulative prefix, and the final theorem proves that the code
together with the complete incoming profile recovers literal prefix
reachability on every represented carrier edge.

This is finite source-image state, not a successor relation stored in the
Cell letter.  Computing the next attachment state from this predecessor state
and the two already finite local factors remains the tracked recurrence.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open GoertzelV24SimpleGraphPortResidualFactorContraction
open GoertzelV24FramedTrail
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

local instance openedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Fixed finite predecessor state on the common Cell-transition carrier.
The persistent ports are exactly the two incoming crossings and the retained
shared rung of the terminal-aware input profile. -/
abbrev SourceLocalLayerSerialTrackedPrefixAttachmentState :=
  TrackedColorPair ->
    BoundedSupportedPortResidualCode (Fin 21) (CorridorPort 2 1)

/-- Interpret a fixed attachment state through the connectivity relation of
the complete terminal-aware incoming profile. -/
def sourceLocalLayerSerialTrackedPrefixFactoredReachability
    (state : SourceLocalLayerSerialTrackedPrefixAttachmentState)
    (input : BoundedCorridorCutProfile 2 1 4)
    (pair : TrackedColorPair) (left right : Fin 21) : Prop :=
  SupportedPortResidualFactoredReachability (state pair)
    (fun leftPort rightPort =>
      input.profile.strandConnected pair leftPort rightPort = true)
    left right

/-- Embed a literal carrier edge into the fixed twenty-one-slot coordinate
system, using the very same carrier equivalence as the finite Cell code. -/
noncomputable def sourceLocalLayerSerialTrackedTransitionSlotAt
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    {edge // edge ∈ sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique offset} -> Fin 21 :=
  fun edge => Fin.castLE
    (sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      graphData minimal caps coloring web corridor hunique offset)
    (carrierCoordinate
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset) edge)

/-- Partial inverse of the fixed-slot embedding.  Slots beyond the literal
carrier cardinality decode to `none` and are therefore inactive. -/
noncomputable def sourceLocalLayerSerialTrackedTransitionEdgeAtSlot?
    (graphData : Data G)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) : Fin 21 ->
      Option {edge // edge ∈
        sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique offset} :=
  fun slot =>
    if hslot : slot.val <
        (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique offset).card then
      some ((carrierCoordinate
        (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique offset)).symm ⟨slot.val, hslot⟩)
    else none

@[simp] theorem sourceLocalLayerSerialTrackedTransitionEdgeAtSlot?_slot
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (edge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    sourceLocalLayerSerialTrackedTransitionEdgeAtSlot? graphData caps coloring
        web corridor hunique offset
        (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
          coloring web corridor hunique offset edge) = some edge := by
  simp [sourceLocalLayerSerialTrackedTransitionEdgeAtSlot?,
    sourceLocalLayerSerialTrackedTransitionSlotAt]

/-- Extract the exact finite predecessor attachment state from the literal
terminal-aware cumulative prefix. -/
noncomputable def sourceLocalLayerSerialTrackedPrefixAttachmentStateAt
    (graphData : Data G)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    SourceLocalLayerSerialTrackedPrefixAttachmentState :=
  let data := sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset
  let edgeAt := fun edge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset} => edge.1
  fun pair =>
    padSupportedPortResidualCode
      (sourceLocalLayerSerialTrackedTransitionEdgeAtSlot? graphData caps coloring
        web corridor hunique offset)
      (exactSupportedPortResidualCode
        (regionalTrackedEdgeGraph web.annular.RS
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          coloring (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2)
        edgeAt data.portEdge)

/-- The actual terminal-aware input profile gives a sound and complete
component relation on its three persistent ports. -/
private theorem sourceLocalLayerSerialTerminalInputProfile_portConnected_exact
    (graphData : Data G)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (pair : TrackedColorPair) :
    let data := sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset
    let graph := regionalTrackedEdgeGraph web.annular.RS data.regionEdges coloring
      (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
    let input := sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor
      hunique offset
    (∀ left right,
      input.profile.strandConnected pair left right = true ->
        graph.Reachable (data.portEdge left) (data.portEdge right)) ∧
    (∀ left right,
      data.portEdge left ∈ graph.support ->
      data.portEdge right ∈ graph.support ->
      graph.Reachable (data.portEdge left) (data.portEdge right) ->
        input.profile.strandConnected pair left right = true) := by
  dsimp only
  let data := sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset
  let graph := regionalTrackedEdgeGraph web.annular.RS data.regionEdges coloring
    (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let input := sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor
    hunique offset
  constructor
  · intro left right hconnected
    have hraw :
        (data.regionalProfile coloring (fun _ => web.tait _)).strandConnected
            pair left right = true := by
      simpa [input, sourceLocalLayerSerialTerminalInputBoundedProfileAt, data]
        using hconnected
    exact (data.regionalProfile_strandConnected_eq_true_iff
      coloring (fun _ => web.tait _) pair left right).1 hraw |>.2.2.2.2
  · intro left right hleftSupport hrightSupport hreachable
    rcases (SimpleGraph.mem_support graph).1 hleftSupport with
      ⟨leftNeighbor, hleftAdj⟩
    rcases (SimpleGraph.mem_support graph).1 hrightSupport with
      ⟨rightNeighbor, hrightAdj⟩
    have hraw :
        (data.regionalProfile coloring (fun _ => web.tait _)).strandConnected
            pair left right = true :=
      (data.regionalProfile_strandConnected_eq_true_iff
        coloring (fun _ => web.tait _) pair left right).2
        ⟨sourceLocalLayerSerialTerminalInputCutDataAt_portsInRegion corridor
            hunique offset left,
          sourceLocalLayerSerialTerminalInputCutDataAt_portsInRegion corridor
            hunique offset right,
          hleftAdj.1.2.1, hrightAdj.1.2.1, hreachable⟩
    simpa [input, sourceLocalLayerSerialTerminalInputBoundedProfileAt, data]
      using hraw

/-- The finite attachment state and the complete incoming profile recover
literal accumulated-prefix reachability on every represented edge of the
common twenty-one-edge transition carrier. -/
theorem sourceLocalLayerSerialTrackedPrefixAttachmentStateAt_factoredReachability_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (pair : TrackedColorPair)
    (left right : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    sourceLocalLayerSerialTrackedPrefixFactoredReachability
        (sourceLocalLayerSerialTrackedPrefixAttachmentStateAt graphData caps
          coloring web corridor hunique offset)
        (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
          offset)
        pair
        (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
          coloring web corridor hunique offset left)
        (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
          coloring web corridor hunique offset right) ↔
      (regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        coloring (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable left.1 right.1 := by
  let data := sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset
  let graph := regionalTrackedEdgeGraph web.annular.RS data.regionEdges coloring
    (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let edgeAt := fun edge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset} => edge.1
  let input := sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor
    hunique offset
  let portConnected := fun leftPort rightPort : CorridorPort 2 1 =>
    input.profile.strandConnected pair leftPort rightPort = true
  have hports := sourceLocalLayerSerialTerminalInputProfile_portConnected_exact
    graphData caps coloring web corridor hunique offset pair
  have hexact :
      graph.Reachable (edgeAt left) (edgeAt right) ↔
        SupportedPortResidualFactoredReachability
          (exactSupportedPortResidualCode graph edgeAt data.portEdge)
          portConnected left right := by
    exact reachable_iff_exactSupportedPortResidualFactoredReachability graph
      edgeAt data.portEdge portConnected hports.1 hports.2 left right
  change SupportedPortResidualFactoredReachability
      (padSupportedPortResidualCode
        (sourceLocalLayerSerialTrackedTransitionEdgeAtSlot? graphData caps
          coloring web corridor hunique offset)
        (exactSupportedPortResidualCode graph edgeAt data.portEdge))
      portConnected
      (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
        coloring web corridor hunique offset left)
      (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
        coloring web corridor hunique offset right) ↔ _
  simp only [SupportedPortResidualFactoredReachability,
    PortResidualFactoredReachability, padSupportedPortResidualCode,
    sourceLocalLayerSerialTrackedTransitionEdgeAtSlot?_slot]
  exact hexact.symm

end

end GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState

end Mettapedia.GraphTheory.FourColor
