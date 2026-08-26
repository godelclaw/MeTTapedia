import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedCumulativeState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePreRebaseState

/-!
# Graph-free tracked update before a Cell boundary rebase

The rooted cumulative state contains the deletion-stable exterior code of the
prefix.  A physical Cell factor contains only local uncoloured geometry and
the Cell colour table.  This file combines those two finite records by adding
the reconstructed Cell and seam adjacency to the prefix exterior code.

The update is guarded by equality of the two dependent carrier cardinalities.
On every literal compatible prefix/Cell splice the guard succeeds and the
result is exactly the source pre-rebase exterior state.  Thus the first stage
of the rolling transition is graph-free and does not retain an ambient graph
or a prefix-specialized local factor.

The following boundary-rebase stage must still compare this state with the
old-coordinate restriction of the expanded role receipt.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedPreRebaseState

open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedBoolColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePrefixState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24ClosedWebLocalLayerSerialColoredCumulativeStateForColor
open GoertzelV24ClosedWebLocalLayerSerialRootedCumulativeState
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

local instance rootedPreRebaseOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Read the reconstructed Cell and seam adjacency on the rooted state's
dependent predecessor carrier. -/
def sourceLocalLayerSerialRootedTrackedLocalAdjacency
    {outputCount : Fin 5}
    (state : SourceLocalLayerSerialRootedCumulativeState)
    (localFactor : SourceLocalLayerSerialCellPhysicalBoolLocalFactor
      outputCount)
    (hcount : state.trackedExterior.vertexCount =
      localFactor.trackedGeometry.vertexCount)
    (pair : TrackedColorPair) :
    Fin state.trackedExterior.vertexCount.val →
      Fin state.trackedExterior.vertexCount.val → Bool :=
  let localCode := sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry
    localFactor.trackedGeometry state.colorCode localFactor.trackedCellColor
  let cast : Fin state.trackedExterior.vertexCount.val →
      Fin localFactor.trackedGeometry.vertexCount.val :=
    Fin.cast (congrArg Fin.val hcount)
  fun left right => decide
    (((localCode.toGraph (pair, false)) ⊔
      (localCode.toGraph (pair, true))).Adj (cast left) (cast right))

/-- Adjoin one physical Cell and its residual seam to the rooted prefix's
deletion-stable tracked exterior code. -/
def sourceLocalLayerSerialRootedTrackedPreRebaseState
    {outputCount : Fin 5}
    (state : SourceLocalLayerSerialRootedCumulativeState)
    (localFactor : SourceLocalLayerSerialCellPhysicalBoolLocalFactor
      outputCount)
    (hcount : state.trackedExterior.vertexCount =
      localFactor.trackedGeometry.vertexCount) :
    SourceLocalLayerSerialTrackedDeletionStablePrefixState where
  vertexCount := state.trackedExterior.vertexCount
  code := fun pair => addInterfaceAdjacency
    (state.trackedExterior.code pair)
    (sourceLocalLayerSerialRootedTrackedLocalAdjacency state localFactor hcount
      pair)

/-- Executable guarded form of the tracked pre-rebase update.  A malformed
state/factor pair with different dependent carrier sizes is rejected. -/
def sourceLocalLayerSerialRootedTrackedPreRebaseState?
    {outputCount : Fin 5}
    (state : SourceLocalLayerSerialRootedCumulativeState)
    (localFactor : SourceLocalLayerSerialCellPhysicalBoolLocalFactor
      outputCount) :
    Option SourceLocalLayerSerialTrackedDeletionStablePrefixState :=
  if hcount : state.trackedExterior.vertexCount =
      localFactor.trackedGeometry.vertexCount then
    some (sourceLocalLayerSerialRootedTrackedPreRebaseState state localFactor
      hcount)
  else none

/-- A compatible splice does not change the exact exterior code of the
accumulated prefix. -/
theorem
    sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt_spliced_eq
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset coloring cellColor) :
    sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt graphData
        minimal caps coloring web corridor hunique offset
        (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          coloring cellColor) =
      sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt graphData
        minimal caps coloring web corridor hunique offset coloring := by
  unfold sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt
  dsimp only
  apply congrArg
  funext pair
  exact regionalTrackedEdgeGraph_spliced_eq_prefix corridor hunique offset
    coloring cellColor hcompatible (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2

/-- Field-level form of `..._spliced_eq`.  This is the form consumed by a
dependent carrier update: the carrier is literally unchanged, and each
tracked colour-pair row is unchanged without transporting the whole family
record. -/
theorem
    sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt_spliced_code_eq
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset coloring cellColor)
    (pair : TrackedColorPair) :
    (sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt graphData
        minimal caps coloring web corridor hunique offset
        (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          coloring cellColor)).code pair =
      (sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt graphData
        minimal caps coloring web corridor hunique offset coloring).code pair := by
  unfold sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt
    boundedInterfaceExteriorFamilyCode
  dsimp only
  rw [regionalTrackedEdgeGraph_spliced_eq_prefix corridor hunique offset
    coloring cellColor hcompatible (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2]

/-- On a literal source Cell, the native graph-free local adjacency is the
same table used by the already verified source recurrence. -/
theorem sourceLocalLayerSerialRootedTrackedLocalAdjacencyAt_eq
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0)
    (hcount :
      (sourceLocalLayerSerialRootedCumulativeStateForColorAt graphData minimal
        caps coloring web corridor hunique offset coloring (fun _ => web.tait _)
        ).trackedExterior.vertexCount =
      (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData minimal
        caps coloring web corridor hunique offset cellColor hcellColor
        ).2.2.trackedGeometry.vertexCount)
    (pair : TrackedColorPair) :
    sourceLocalLayerSerialRootedTrackedLocalAdjacency
        (sourceLocalLayerSerialRootedCumulativeStateForColorAt graphData minimal
          caps coloring web corridor hunique offset coloring
            (fun _ => web.tait _))
        (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData minimal
          caps coloring web corridor hunique offset cellColor hcellColor).2.2
        hcount pair =
      sourceLocalLayerSerialTrackedLocalAdjacencyForColorAt graphData minimal
        caps coloring web corridor hunique offset
        (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          coloring cellColor) pair := by
  classical
  let rooted := sourceLocalLayerSerialRootedCumulativeStateForColorAt graphData
    minimal caps coloring web corridor hunique offset coloring
      (fun _ => web.tait _)
  let factor := (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt graphData
    minimal caps coloring web corridor hunique offset cellColor hcellColor).2.2
  let native := sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry
    factor.trackedGeometry rooted.colorCode factor.trackedCellColor
  let source := sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData
    minimal caps coloring web corridor hunique offset
      (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset coloring
        cellColor)
  funext left right
  cases hcount
  change Fin native.vertexCount.val at left right
  have hgraph (seam : Bool) :
      native.toGraph (pair, seam) = source.graph (pair, seam) := by
    simpa [native, source, rooted, factor,
      sourceLocalLayerSerialRootedCumulativeStateForColorAt,
      sourceLocalLayerSerialColoredCumulativeStateForColorAt,
      sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt] using
      (sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometryAt_toGraph_eq
        graphData minimal caps coloring web corridor hunique offset cellColor
          (pair, seam))
  change decide ((native.toGraph (pair, false) ⊔
      native.toGraph (pair, true)).Adj left right) =
    decide ((source.graph (pair, false) ⊔ source.graph (pair, true)).Adj
      left right)
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, SimpleGraph.sup_adj]
  exact or_congr
    (Eq.to_iff (congrArg (fun graph => graph.Adj left right) (hgraph false)))
    (Eq.to_iff (congrArg (fun graph => graph.Adj left right) (hgraph true)))

/-- The guarded graph-free update succeeds on every literal compatible Cell
and is exactly the already verified source pre-rebase exterior state. -/
theorem sourceLocalLayerSerialRootedTrackedPreRebaseState?_at
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset coloring cellColor)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0) :
    let rooted := sourceLocalLayerSerialRootedCumulativeStateForColorAt
      graphData minimal caps coloring web corridor hunique offset coloring
        (fun _ => web.tait _)
    let factor := (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
      graphData minimal caps coloring web corridor hunique offset cellColor
        hcellColor).2.2
    sourceLocalLayerSerialRootedTrackedPreRebaseState? rooted factor =
      some (sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt
        graphData minimal caps coloring web corridor hunique offset
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            coloring cellColor)) := by
  classical
  let rooted := sourceLocalLayerSerialRootedCumulativeStateForColorAt
    graphData minimal caps coloring web corridor hunique offset coloring
      (fun _ => web.tait _)
  let factor := (sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
    graphData minimal caps coloring web corridor hunique offset cellColor
      hcellColor).2.2
  let spliced := sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
    coloring cellColor
  change sourceLocalLayerSerialRootedTrackedPreRebaseState? rooted factor =
    some (sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt
      graphData minimal caps coloring web corridor hunique offset spliced)
  unfold sourceLocalLayerSerialRootedTrackedPreRebaseState?
  split <;> rename_i hcount
  · congr 1
    unfold sourceLocalLayerSerialRootedTrackedPreRebaseState
      sourceLocalLayerSerialTrackedDeletionStablePreRebaseStateForColorAt
    congr 1
    funext pair
    rw [sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt_spliced_code_eq
      graphData minimal caps coloring web corridor hunique offset cellColor
        hcompatible pair]
    change addInterfaceAdjacency
        ((sourceLocalLayerSerialTrackedDeletionStablePrefixStateForColorAt
          graphData minimal caps coloring web corridor hunique offset
            coloring).code pair) _ = _
    apply congrArg (fun adjacency => addInterfaceAdjacency _ adjacency)
    funext left right
    calc
      _ = sourceLocalLayerSerialTrackedLocalAdjacencyForColorAt graphData minimal
            caps coloring web corridor hunique offset spliced pair left right := by
          exact congrFun (congrFun
            (sourceLocalLayerSerialRootedTrackedLocalAdjacencyAt_eq graphData
              minimal caps coloring web corridor hunique offset cellColor
                hcellColor hcount pair) left) right
      _ = _ := by
        apply Bool.eq_iff_iff.mpr
        simp only [sourceLocalLayerSerialTrackedLocalAdjacencyForColorAt,
          decide_eq_true_eq, SimpleGraph.sup_adj]
  · exfalso
    apply hcount
    rfl

end

end GoertzelV24ClosedWebLocalLayerSerialRootedPreRebaseState

end Mettapedia.GraphTheory.FourColor
