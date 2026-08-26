import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellPrefixParametricNativeFactorization
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseState

/-!
# Prefix-parametric rooted interaction update before rebase

The complete forty-nine-coordinate rooted update is exact for an arbitrary
cumulative prefix colour function and a compatible literal Cell colouring.
The local factor remains prefix-independent; only the incoming rooted state
contains prefix data.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseColorParametric

open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedBoolColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellPrefixParametricNativeCode
open GoertzelV24ClosedWebLocalLayerSerialCellPrefixParametricNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24ClosedWebLocalLayerSerialColoredCumulativeStateForColor
open GoertzelV24ClosedWebLocalLayerSerialRootedCumulativeState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24ClosedWebLocalLayerSerialRootedPreRebaseState
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorUpdate
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance rootedInteractionPreRebaseColorParametricOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The finite local adjacency reconstructed from a rooted arbitrary-prefix
state and the prefix-independent Cell factor is the source local table of the
literal splice. -/
theorem sourceLocalLayerSerialRootedTrackedLocalAdjacencyForColorAt_eq
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
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0)
    (hcount :
      (sourceLocalLayerSerialRootedCumulativeStateForColorAt graphData minimal
        caps coloring web corridor hunique offset prefixColor hprefixCrossing
        ).trackedExterior.vertexCount =
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
        minimal caps coloring web corridor hunique offset prefixColor
          hprefixCrossing cellColor hcellColor).2.2.trackedGeometry.vertexCount)
    (pair : TrackedColorPair) :
    sourceLocalLayerSerialRootedTrackedLocalAdjacency
        (sourceLocalLayerSerialRootedCumulativeStateForColorAt graphData minimal
          caps coloring web corridor hunique offset prefixColor hprefixCrossing)
        (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
          minimal caps coloring web corridor hunique offset prefixColor
            hprefixCrossing cellColor hcellColor).2.2
        hcount pair =
      sourceLocalLayerSerialTrackedLocalAdjacencyForColorAt graphData minimal
        caps coloring web corridor hunique offset
        (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          prefixColor cellColor) pair := by
  classical
  let rooted := sourceLocalLayerSerialRootedCumulativeStateForColorAt graphData
    minimal caps coloring web corridor hunique offset prefixColor hprefixCrossing
  let factor :=
    (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
      minimal caps coloring web corridor hunique offset prefixColor
        hprefixCrossing cellColor hcellColor).2.2
  let native := sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry
    factor.trackedGeometry rooted.colorCode factor.trackedCellColor
  let spliced := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    prefixColor cellColor
  let source := sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData
    minimal caps coloring web corridor hunique offset spliced
  funext left right
  cases hcount
  change Fin native.vertexCount.val at left right
  have hgraph (seam : Bool) :
      native.toGraph (pair, seam) = source.graph (pair, seam) := by
    simpa [native, source, rooted, factor, spliced,
      sourceLocalLayerSerialRootedCumulativeStateForColorAt,
      sourceLocalLayerSerialColoredCumulativeStateForColorAt,
      sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt] using
      (sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometryForColorAt_toGraph_eq
        graphData minimal caps coloring web corridor hunique offset prefixColor
          cellColor (pair, seam))
  change decide ((native.toGraph (pair, false) ⊔
      native.toGraph (pair, true)).Adj left right) =
    decide ((source.graph (pair, false) ⊔ source.graph (pair, true)).Adj
      left right)
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, SimpleGraph.sup_adj]
  exact or_congr
    (Eq.to_iff (congrArg (fun graph => graph.Adj left right) (hgraph false)))
    (Eq.to_iff (congrArg (fun graph => graph.Adj left right) (hgraph true)))

/-- Native local adjacency reconstructed from arbitrary prefix and Cell colour
tables is the literal local graph of their right-biased splice. -/
theorem
    sourceLocalLayerSerialRootedInteractionLocalAdjacencyForColorAt_eq_true_iff
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
    (hnext : offset.val + 1 < blockLength - 3)
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0)
    (hcount :
      (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
        caps coloring web corridor hunique offset hnext prefixColor
          hprefixCrossing).trackedExterior.vertexCount =
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
        minimal caps coloring web corridor hunique offset prefixColor
          hprefixCrossing cellColor hcellColor).2.2.trackedGeometry.vertexCount)
    (pair : TrackedColorPair)
    (left right : Fin
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext).card) :
    sourceLocalLayerSerialRootedInteractionLocalAdjacency
        (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
          caps coloring web corridor hunique offset hnext prefixColor
            hprefixCrossing)
        (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
          minimal caps coloring web corridor hunique offset prefixColor
            hprefixCrossing cellColor hcellColor).2.2
        hcount pair left right = true ↔
      (sourceLocalLayerSerialTrackedLocalGraphForColorAt caps coloring web
        corridor hunique offset
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            prefixColor cellColor) pair).Adj
        (((carrierCoordinate
          (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
            caps coloring web corridor hunique offset hnext)).symm left).1)
        (((carrierCoordinate
          (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
            caps coloring web corridor hunique offset hnext)).symm right).1) := by
  classical
  let state := sourceLocalLayerSerialRootedInteractionStateForColorAt graphData
    minimal caps coloring web corridor hunique offset hnext prefixColor
      hprefixCrossing
  let factor :=
    (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
      minimal caps coloring web corridor hunique offset prefixColor
        hprefixCrossing cellColor hcellColor).2.2
  let current := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique offset
  let interaction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  let spliced := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    prefixColor cellColor
  let extra := sourceLocalLayerSerialTrackedLocalGraphForColorAt caps coloring web
    corridor hunique offset spliced pair
  let oldVertex := fun slot : Fin current.card =>
    ((carrierCoordinate current).symm slot).1
  let newVertex := fun slot : Fin interaction.card =>
    ((carrierCoordinate interaction).symm slot).1
  have hcoordinate : ∀ old,
      newVertex (state.currentCoordinate old) = oldVertex old := by
    intro old
    exact sourceLocalLayerSerialRootedInteractionStateForColorAt_currentEdge
      graphData minimal caps coloring web corridor hunique offset hnext
        prefixColor hprefixCrossing old
  have hnewInjective : Function.Injective newVertex := by
    intro first second hedge
    apply (carrierCoordinate interaction).symm.injective
    exact Subtype.ext hedge
  have hsupport : extra.support ⊆ Set.range oldVertex := by
    exact sourceLocalLayerSerialTrackedLocalGraph_support_subset_range graphData
      caps coloring web corridor hunique offset spliced pair
  have hadjacency : ∀ oldLeft oldRight,
      sourceLocalLayerSerialRootedTrackedLocalAdjacency
          state.toSourceLocalLayerSerialRootedCumulativeState factor hcount pair
          oldLeft oldRight = true ↔
        extra.Adj (oldVertex oldLeft) (oldVertex oldRight) := by
    intro oldLeft oldRight
    change Fin current.card at oldLeft oldRight
    change
      sourceLocalLayerSerialRootedTrackedLocalAdjacency
          (sourceLocalLayerSerialRootedCumulativeStateForColorAt graphData
            minimal caps coloring web corridor hunique offset prefixColor
              hprefixCrossing)
          (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt
            graphData minimal caps coloring web corridor hunique offset
              prefixColor hprefixCrossing cellColor hcellColor).2.2
          hcount pair oldLeft oldRight = true ↔
      extra.Adj (oldVertex oldLeft) (oldVertex oldRight)
    have hnative :=
      sourceLocalLayerSerialRootedTrackedLocalAdjacencyForColorAt_eq graphData
        minimal caps coloring web corridor hunique offset prefixColor
          hprefixCrossing cellColor hcellColor hcount pair
    have hnativeAt := congrFun (congrFun hnative oldLeft) oldRight
    rw [hnativeAt]
    simpa [extra, oldVertex, current, spliced] using
      (sourceLocalLayerSerialTrackedLocalAdjacency_exact graphData minimal
        caps coloring web corridor hunique offset spliced pair oldLeft oldRight)
  exact liftInterfaceAdjacency_eq_true_iff extra oldVertex newVertex
    state.currentCoordinate hcoordinate hnewInjective hsupport
    (sourceLocalLayerSerialRootedTrackedLocalAdjacency
      state.toSourceLocalLayerSerialRootedCumulativeState factor hcount pair)
    hadjacency left right

/-- Each row of the finite enlarged update is the exact literal pre-rebase row
for an arbitrary compatible cumulative prefix. -/
theorem
    sourceLocalLayerSerialRootedInteractionPreRebaseStateForColorAt_code_eq
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
    (hnext : offset.val + 1 < blockLength - 3)
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset prefixColor cellColor)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0)
    (hcount :
      (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
        caps coloring web corridor hunique offset hnext prefixColor
          hprefixCrossing).trackedExterior.vertexCount =
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
        minimal caps coloring web corridor hunique offset prefixColor
          hprefixCrossing cellColor hcellColor).2.2.trackedGeometry.vertexCount)
    (pair : TrackedColorPair) :
    (sourceLocalLayerSerialRootedInteractionPreRebaseState
      (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
        caps coloring web corridor hunique offset hnext prefixColor
          hprefixCrossing)
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
        minimal caps coloring web corridor hunique offset prefixColor
          hprefixCrossing cellColor hcellColor).2.2
      hcount).code pair =
      (sourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
        graphData minimal caps coloring web corridor hunique offset hnext
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            prefixColor cellColor)).code pair := by
  classical
  let interaction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  let edgeAt := fun slot : Fin interaction.card =>
    ((carrierCoordinate interaction).symm slot).1
  let spliced := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    prefixColor cellColor
  let adjacency := sourceLocalLayerSerialRootedInteractionLocalAdjacency
    (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
      caps coloring web corridor hunique offset hnext prefixColor
        hprefixCrossing)
    (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
      minimal caps coloring web corridor hunique offset prefixColor
        hprefixCrossing cellColor hcellColor).2.2
    hcount pair
  have hprefix : regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
      spliced (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 =
      regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
      prefixColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 :=
    regionalTrackedEdgeGraph_spliced_eq_prefix corridor hunique offset
      prefixColor cellColor hcompatible (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
  change addInterfaceAdjacency
      (exactInterfaceExteriorCode
        (regionalTrackedEdgeGraph web.annular.RS
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          prefixColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2)
        edgeAt)
      adjacency =
    exactInterfaceExteriorCode
      (regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        spliced (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2)
      edgeAt
  rw [sourceLocalLayerSerialPreRebaseTrackedGraph_eq_three_factor corridor
    hunique offset spliced (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2, sup_assoc, hprefix]
  apply addInterfaceAdjacency_exact_code_eq
  · exact
      sourceLocalLayerSerialTrackedLocalGraph_support_subset_interaction_range
        graphData caps coloring web corridor hunique offset hnext spliced pair
  · intro left right
    exact
      sourceLocalLayerSerialRootedInteractionLocalAdjacencyForColorAt_eq_true_iff
        graphData minimal caps coloring web corridor hunique offset hnext
          prefixColor hprefixCrossing cellColor hcellColor hcount pair left right

/-- The guarded complete-carrier update succeeds and returns the canonical
pre-rebase state for every compatible cumulative prefix. -/
theorem
    sourceLocalLayerSerialRootedInteractionPreRebaseStateForColor?_at
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
    (hnext : offset.val + 1 < blockLength - 3)
    (prefixColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hprefixCrossing : ∀ step,
      prefixColor ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0)
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset prefixColor cellColor)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0) :
    let state := sourceLocalLayerSerialRootedInteractionStateForColorAt
      graphData minimal caps coloring web corridor hunique offset hnext
        prefixColor hprefixCrossing
    let factor :=
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
        minimal caps coloring web corridor hunique offset prefixColor
          hprefixCrossing cellColor hcellColor).2.2
    sourceLocalLayerSerialRootedInteractionPreRebaseState? state factor =
      some (sourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
        graphData minimal caps coloring web corridor hunique offset hnext
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            prefixColor cellColor)) := by
  classical
  let state := sourceLocalLayerSerialRootedInteractionStateForColorAt graphData
    minimal caps coloring web corridor hunique offset hnext prefixColor
      hprefixCrossing
  let factor :=
    (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterForColorAt graphData
      minimal caps coloring web corridor hunique offset prefixColor
        hprefixCrossing cellColor hcellColor).2.2
  let expected := sourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
    graphData minimal caps coloring web corridor hunique offset hnext
      (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
        prefixColor cellColor)
  change sourceLocalLayerSerialRootedInteractionPreRebaseState? state factor =
    some expected
  unfold sourceLocalLayerSerialRootedInteractionPreRebaseState?
  split <;> rename_i hcount
  · congr 1
    unfold sourceLocalLayerSerialRootedInteractionPreRebaseState
    congr 1
    funext pair
    exact
      sourceLocalLayerSerialRootedInteractionPreRebaseStateForColorAt_code_eq
        graphData minimal caps coloring web corridor hunique offset hnext
          prefixColor hprefixCrossing cellColor hcompatible hcellColor hcount pair
  · exfalso
    apply hcount
    rfl

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseColorParametric

end Mettapedia.GraphTheory.FourColor
