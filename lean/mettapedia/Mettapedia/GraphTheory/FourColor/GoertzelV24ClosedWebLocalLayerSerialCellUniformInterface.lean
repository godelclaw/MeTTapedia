import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellPastOverlap
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFaceCollarCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceTransitionCarrier

/-!
# A uniform boundary interface for one literal Cell and its rebase

Addendum XXV uses a finite cut profile because a bounded-width corridor slab
can meet its accumulated prefix only through a bounded boundary.  The local
Cell and boundary-rebase developments previously proved the two halves of
this assertion on separate carriers.  This file packages their union and
records a bound independent of the corridor length and the Cell offset.

For tracked primal-edge connectivity, the literal Cell and its outgoing seam
use at most twenty-one edges, while the following rebase uses a collar of at
most twenty-eight edges.  Their union therefore has at most forty-nine edges.
For facial connectivity, the analogous bounds are twenty-four darts on each
side, hence forty-eight dart occurrences.

The bounds are deliberately conservative: overlaps can only make the actual
carriers smaller.  More importantly, the portal-completeness theorems prove
that every genuine prefix--Cell seam adjacency touches one of the two outgoing
ports, and the past-overlap theorem proves that strict history recurring in
the successor carrier is already visible in the current carrier or the
four-edge switch.  Thus this is a termination certificate for the local
receipt size, not another receipt enlargement.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellPastOverlap
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialCellUniformInterfaceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance closedWebLocalLayerSerialCellUniformInterfaceOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

namespace Instance

namespace LocalLayerFormation

/-- The complete tracked interaction carrier for one literal Cell update and
the immediately following boundary rebase. -/
noncomputable def sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
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
    (hnext : offset.val + 1 < blockLength - 3) :
    Finset caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet :=
  sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring web
      corridor hunique offset ∪
    sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset hnext

/-- The tracked carrier has a corridor-length-independent size bound. -/
theorem sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
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
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext).card ≤ 49 := by
  calc
    (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext).card ≤
        (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique offset).card +
        (sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset
          hnext).card := Finset.card_union_le _ _
    _ ≤ 21 + 28 := Nat.add_le_add
      (sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
        graphData minimal caps coloring web corridor hunique offset)
      (sourceLocalLayerBoundaryRebaseTrackedCollarAt_card_le_twentyEight
        corridor hunique offset hnext)
    _ = 49 := by norm_num

/-- The complete facial-dart interaction carrier for the same Cell update and
boundary rebase. -/
noncomputable def sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) : Finset web.annular.RS.D :=
  sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset ∪
    sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset hnext

/-- The facial carrier has a corridor-length-independent size bound whenever
the literal Cell has its source width bound. -/
theorem
    sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt_card_le_fortyEight_of_cell
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell :
      (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
      offset hnext).card ≤ 48 := by
  calc
    (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
      offset hnext).card ≤
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
          ).card +
        (sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset hnext
          ).card := Finset.card_union_le _ _
    _ ≤ 24 + 24 := Nat.add_le_add
      (sourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour corridor
        hunique offset hcell)
      (card_sourceLocalLayerBoundaryRebaseFaceCollarAt_le_twentyFour corridor
        hunique offset hnext)
    _ = 48 := by norm_num

/-- Minimal-counterexample specialization of the structural facial-carrier
bound. -/
theorem sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt_card_le_fortyEight
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
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
      offset hnext).card ≤ 48 := by
  have hcell :
      (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6 :=
    sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps coloring web
      corridor hunique offset
  exact
    sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt_card_le_fortyEight_of_cell
      corridor hunique offset hnext hcell

/-- Every tracked prefix--Cell seam adjacency meets one of the two named
outgoing ports; this is the structural interface statement behind the
fourteen-edge seam carrier. -/
theorem sourceLocalLayerSerialCell_trackedSeam_adj_meets_boundedBoundary
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (first second : Color) {left right : G.edgeSet}
    (hadj : (sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
      color first second).Adj left right) :
    ∃ step : Fin 2,
      left = sourceLocalLayerRightCrossingAt corridor hunique offset step ∨
        right = sourceLocalLayerRightCrossingAt corridor hunique offset step :=
  sourceLocalLayerSerialTerminalTrackedSeamAt_adj_touches_rightCrossing
    corridor hunique offset color first second hadj

/-- Root-independent facial version: every prefix--Cell seam step meets a dart
over one of the same two outgoing ports. -/
theorem sourceLocalLayerSerialCell_faceSeam_adj_meets_boundedBoundary
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) {left right : web.annular.RS.D}
    (hadj : (sourceLocalLayerSerialTerminalFaceDartSeamAt corridor hunique
      offset).Adj left right) :
    ∃ step : Fin 2,
      web.annular.RS.edgeOf left =
          sourceLocalLayerRightCrossingAt corridor hunique offset step ∨
        web.annular.RS.edgeOf right =
          sourceLocalLayerRightCrossingAt corridor hunique offset step :=
  sourceLocalLayerSerialTerminalFaceDartSeamAt_adj_touches_rightCrossing
    corridor hunique offset hadj

/-- The complete tracked seam factor is supported on the uniform interaction
carrier. -/
theorem sourceLocalLayerSerialCell_trackedSeam_support_subset_uniformInterface
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
    (hnext : offset.val + 1 < blockLength - 3)
    (color : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet →
      Color) (pair : TrackedColorPair) :
    (sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset color
      (trackedColorPairColors pair).1 (trackedColorPairColors pair).2).support ⊆
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext := by
  intro edge hedge
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact sourceLocalLayerSerialTerminalTrackedSeamAt_support_subset_outgoingCarrier
    corridor hunique offset color (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2 hedge

/-- Both graph factors of the tracked rebase recurrence use the same uniform
interaction carrier. -/
theorem sourceLocalLayerSerialCell_trackedRebase_support_subset_uniformInterface
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
    (hnext : offset.val + 1 < blockLength - 3)
    (color : caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet →
      Color) (pair : TrackedColorPair) :
    (trackedCoreComponentGraphForColorAt corridor hunique offset hnext color pair
        ).support ⊆
        sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
          caps coloring web corridor hunique offset hnext ∧
      (localTrackedGraphForColorAt corridor hunique offset hnext color pair
        ).support ⊆
        sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
          caps coloring web corridor hunique offset hnext := by
  constructor
  · intro edge hedge
    exact Finset.mem_union_right _
      (trackedCoreComponentGraphForColorAt_support_subset_collar corridor hunique
        offset hnext color pair hedge)
  · intro edge hedge
    exact Finset.mem_union_right _
      (localTrackedGraphForColorAt_support_subset_collar corridor hunique offset
        hnext color pair hedge)

/-- The complete facial seam factor is supported on the uniform dart
interaction carrier. -/
theorem sourceLocalLayerSerialCell_faceSeam_support_subset_uniformInterface
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceLocalLayerSerialTerminalFaceDartSeamAt corridor hunique offset
      ).support ⊆
      sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        offset hnext := by
  intro dart hdart
  exact Finset.mem_union_left _
    (sourceLocalLayerFaceDartSeam_support_subset_transitionCarrier corridor
      hunique offset hdart)

/-- Both graph factors of the facial rebase recurrence use the same uniform
dart interaction carrier. -/
theorem sourceLocalLayerSerialCell_faceRebase_support_subset_uniformInterface
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceLocalLayerBoundaryRebaseCoreComponentGraphAt corridor hunique offset
        hnext).support ⊆
        sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
          offset hnext ∧
      (sourceLocalLayerBoundaryRebaseLocalFaceGraphAt corridor hunique offset
        hnext).support ⊆
        sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
          offset hnext := by
  constructor
  · intro dart hdart
    exact Finset.mem_union_right _
      (sourceLocalLayerBoundaryRebaseCoreComponentGraphAt_support_subset_collar
        corridor hunique offset hnext hdart)
  · intro dart hdart
    exact Finset.mem_union_right _
      (sourceLocalLayerBoundaryRebaseLocalFaceGraphAt_support_subset_collar
        corridor hunique offset hnext hdart)

/-- Strict prefix history cannot enter the successor moving carrier through
an unnamed coordinate: it is already in the current carrier or in the
four-edge switch. -/
theorem sourceLocalLayerSerialCellRebase_strictHistory_meets_boundedBoundary
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
    (hnext : offset.val + 1 < blockLength - 3) :
    ∀
      (targetEdge : {edge // edge ∈
        sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
          web corridor hunique (sourceLocalLayerNextOffset offset hnext)})
      (prior : Fin (blockLength - 3)),
      prior.val < offset.val →
      targetEdge.1 ∈ sourceLocalLayerCellRegionAt corridor hunique prior →
        targetEdge.1 ∈ sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique
            offset hnext ∨
          targetEdge.1 ∈
            sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
              coloring web corridor hunique offset :=
  sourceLocalLayerSerialCellRebase_pastCellOverlap graphData minimal caps
    coloring web corridor hunique offset hnext

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
