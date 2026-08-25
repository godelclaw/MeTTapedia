import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState

/-!
# Colour-parametric cumulative tracked attachments

After a physical Cell is spliced onto an accumulated prefix, the following
boundary rebase is evaluated at the spliced colouring rather than the original
ambient colouring.  The terminal profile was already generalized to that
colouring.  This file makes the richer twenty-one-slot tracked predecessor
state colour-parametric as well.

The crown theorem proves exact reachability reconstruction for every supplied
colour function.  Thus the target of one alternating Cell--rebase letter can
be represented in the same cumulative-state type as its source.  No recurrence
from an arbitrary finite predecessor state and no reachable closure is claimed
here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialTrackedPrefixAttachmentColorParametric

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FramedTrail
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24SimpleGraphPortResidualFactorContraction
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance trackedPrefixColorParametricOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Extract the cumulative tracked attachment state at an arbitrary colour
function on the same literal prefix region. -/
noncomputable def sourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt
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
    (offset : Fin (blockLength - 3))
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
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
          color (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2)
        edgeAt data.portEdge)

@[simp]
theorem sourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt_ambient
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
    sourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt graphData caps
        coloring web corridor hunique offset coloring =
      sourceLocalLayerSerialTrackedPrefixAttachmentStateAt graphData caps
        coloring web corridor hunique offset := by
  rfl

/-- At an arbitrary colour function, the complete terminal profile is sound
and complete for connectivity among its three persistent ports. -/
private theorem terminalInputProfileForColorAt_portConnected_exact
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
    (offset : Fin (blockLength - 3))
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (pair : TrackedColorPair) :
    let data := sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
      offset
    let graph := regionalTrackedEdgeGraph web.annular.RS data.regionEdges color
      (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
    let input := terminalInputBoundedProfileForColorAt corridor hunique offset
      color hcrossing
    (∀ left right,
      input.profile.strandConnected pair left right = true →
        graph.Reachable (data.portEdge left) (data.portEdge right)) ∧
    (∀ left right,
      data.portEdge left ∈ graph.support →
      data.portEdge right ∈ graph.support →
      graph.Reachable (data.portEdge left) (data.portEdge right) →
        input.profile.strandConnected pair left right = true) := by
  dsimp only
  let data := sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset
  let graph := regionalTrackedEdgeGraph web.annular.RS data.regionEdges color
    (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let input := terminalInputBoundedProfileForColorAt corridor hunique offset
    color hcrossing
  constructor
  · intro left right hconnected
    exact (data.regionalProfile_strandConnected_eq_true_iff color hcrossing pair
      left right).1 hconnected |>.2.2.2.2
  · intro left right hleftSupport hrightSupport hreachable
    rcases (SimpleGraph.mem_support graph).1 hleftSupport with
      ⟨leftNeighbor, hleftAdj⟩
    rcases (SimpleGraph.mem_support graph).1 hrightSupport with
      ⟨rightNeighbor, hrightAdj⟩
    exact (data.regionalProfile_strandConnected_eq_true_iff color hcrossing pair
      left right).2
        ⟨sourceLocalLayerSerialTerminalInputCutDataAt_portsInRegion corridor
            hunique offset left,
          sourceLocalLayerSerialTerminalInputCutDataAt_portsInRegion corridor
            hunique offset right,
          hleftAdj.1.2.1, hrightAdj.1.2.1, hreachable⟩

/-- The colour-parametric finite attachment state and terminal profile recover
literal accumulated-prefix reachability on every represented carrier edge. -/
theorem sourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt_factoredReachability_iff
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (pair : TrackedColorPair)
    (left right : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    sourceLocalLayerSerialTrackedPrefixFactoredReachability
        (sourceLocalLayerSerialTrackedPrefixAttachmentStateForColorAt graphData
          caps coloring web corridor hunique offset color)
        (terminalInputBoundedProfileForColorAt corridor hunique offset color
          hcrossing)
        pair
        (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
          coloring web corridor hunique offset left)
        (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
          coloring web corridor hunique offset right) ↔
      (regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable left.1 right.1 := by
  let data := sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset
  let graph := regionalTrackedEdgeGraph web.annular.RS data.regionEdges color
    (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let edgeAt := fun edge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset} => edge.1
  let input := terminalInputBoundedProfileForColorAt corridor hunique offset
    color hcrossing
  let portConnected := fun leftPort rightPort : CorridorPort 2 1 =>
    input.profile.strandConnected pair leftPort rightPort = true
  have hports := terminalInputProfileForColorAt_portConnected_exact graphData
    caps coloring web corridor hunique offset color hcrossing pair
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


end GoertzelV24ClosedWebLocalLayerSerialTrackedPrefixAttachmentColorParametric

end Mettapedia.GraphTheory.FourColor
