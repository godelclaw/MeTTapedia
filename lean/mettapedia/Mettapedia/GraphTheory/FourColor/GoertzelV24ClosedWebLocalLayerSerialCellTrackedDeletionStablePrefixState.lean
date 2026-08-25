import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialTrackedPrefixAttachmentColorParametric
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactor

/-!
# A deletion-stable tracked cumulative-prefix state

The former tracked prefix state stores the component partition seen from the
twenty-one-slot Cell carrier.  A later Cell boundary switch may delete a
carrier edge, and a pre-deletion component partition does not determine the
components left after that deletion.

This file extracts the stronger finite state required by the cumulative
`Count` transition.  For every tracked colour pair it records literal
adjacency on the common carrier and attachment through components strictly
outside that carrier.  The generic interface-contraction theorem then recovers
exact prefix reachability for every deletion mask by a closure over only the
surviving carrier coordinates.

The state is still bounded by twenty-one vertices and is independent of the
length of the accumulated corridor prefix.  This file constructs and verifies
the source state; the next recurrence must combine it with the prefix-
independent Cell and seam factors before applying a boundary-rebase mask.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePrefixState

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance trackedDeletionStablePrefixStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance trackedDeletionStablePrefixStateOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The finite deletion-stable tracked state of one cumulative prefix. -/
abbrev SourceLocalLayerSerialTrackedDeletionStablePrefixState :=
  BoundedInterfaceExteriorFamilyCode 21 TrackedColorPair

/-- Extract the exact deletion-stable state of an arbitrary compatible prefix
colouring on the literal Cell transition carrier. -/
noncomputable def sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
    SourceLocalLayerSerialTrackedDeletionStablePrefixState :=
  let carrier :=
    sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring web
      corridor hunique offset
  boundedInterfaceExteriorFamilyCode carrier 21
    (sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      graphData minimal caps coloring web corridor hunique offset)
    (fun pair =>
      regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2)

/-- The state carries the literal cardinality of the common Cell carrier. -/
@[simp]
theorem sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt_vertexCount
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
    (sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt
      graphData minimal caps coloring web corridor hunique offset color
      ).vertexCount.val =
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset).card :=
  rfl

/-- The source-extracted bounded state exactly reconstructs prefix
reachability after every mask on the common Cell carrier. -/
theorem sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt_reachable_iff
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
    (pair : TrackedColorPair)
    (removed : Fin
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset).card → Bool)
    (left right : SurvivingInterfaceSlot
      (fun slot : Fin
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset).card =>
        ((carrierCoordinate
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset)).symm slot).1)
      removed) :
    let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
      caps coloring web corridor hunique offset
    let graph := regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
      color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
    let edgeAt := fun slot : Fin carrier.card =>
      ((carrierCoordinate carrier).symm slot).1
    (restrictedByMask graph edgeAt removed).Reachable
        (edgeAt left.1) (edgeAt right.1) ↔
      Relation.ReflTransGen
        (fun first second : SurvivingInterfaceSlot edgeAt removed =>
          InterfaceExteriorFactoredStep
            ((sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt
              graphData minimal caps coloring web corridor hunique offset color
              ).code pair)
            first.1 second.1)
        left right := by
  dsimp only
  exact boundedInterfaceExteriorFamilyCode_reachable_iff
    (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring web
      corridor hunique offset)
    21
    (sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      graphData minimal caps coloring web corridor hunique offset)
    (fun pair =>
      regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2)
    pair removed left right

end

end GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePrefixState

end Mettapedia.GraphTheory.FourColor
