import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedTargetCode

/-!
# Contract the uniform facial successor to the next rolling dart carrier

The exact facial Cell--rebase recurrence uses at most forty-eight dart
coordinates, while the next cumulative state uses its rolling at-most-
twenty-four-dart transition carrier.  This file constructs the partial map
from the latter carrier into the former and proves that every unmapped target
dart is inactive in the literal successor face graph.

The load-bearing geometry is occurrence-sensitive.  A dart in the target
facial carrier lies over an edge of the target tracked carrier.  If that dart
is active, the strengthened historical-overlap theorem places its edge either
in the four-edge switch or in the current Cell.  All dart occurrences in
those two cases lie in the rebase collar or the current facial carrier,
respectively.  No converse from edge adjacency to facial-neighborhood
membership is assumed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCode

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellPastOverlap
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorForget
open GoertzelV24InterfaceDeletionComponentFactorForgetExterior
open GoertzelV24InterfaceExteriorSupportedPortProjection
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationFaceRegionalDartCarrier
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance uniformFaceTargetCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance uniformFaceTargetCodeOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The edge underlying a target facial dart belongs to the corresponding
target tracked carrier. -/
theorem sourceLocalLayerSerialFaceTransitionCarrierAt_edgeOf_mem_tracked
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
    (dart : web.annular.RS.D)
    (hdart : dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset) :
    web.annular.RS.edgeOf dart ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset := by
  rw [sourceLocalLayerSerialFaceTransitionCarrierAt, Finset.mem_union] at hdart
  rcases hdart with hcell | houtgoing
  · exact Finset.mem_union_left _ <| Finset.mem_union_left _ <|
      (mem_dartsOnEdges_iff web.annular.RS _ dart).1 hcell
  · apply Finset.mem_union_left _
    apply Finset.mem_union_right _
    have hedge :=
      edgeOf_mem_edgeAdjacencyClosedCarrier_of_mem_closedDartCarrier
        web.annular.RS
        (indexedCrossingEdgeSet
          (sourceLocalLayerRightCrossingAt corridor hunique offset))
        dart
        (by simpa [sourceLocalLayerSerialFaceOutgoingDartCarrierAt] using
          houtgoing)
    simpa [sourceLocalLayerSerialOutgoingEdgeCarrierAt] using hedge

/-- Every active target dart is already named by the fixed current
Cell--rebase facial carrier.  This is the occurrence-sensitive termination
certificate for the rolling facial state. -/
theorem sourceLocalLayerSerialCellRebase_activeFaceTarget_mem_uniform
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
    (dart : web.annular.RS.D)
    (htarget : dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext))
    (hactive : dart ∈
      (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique
        offset hnext).support) :
    dart ∈ sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
      hunique offset hnext := by
  let targetEdge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique (sourceLocalLayerNextOffset offset hnext)} :=
    ⟨web.annular.RS.edgeOf dart,
      sourceLocalLayerSerialFaceTransitionCarrierAt_edgeOf_mem_tracked graphData
        caps coloring web corridor hunique
          (sourceLocalLayerNextOffset offset hnext) dart htarget⟩
  rcases (SimpleGraph.mem_support _).1 hactive with ⟨other, hadj⟩
  have hregion : targetEdge.1 ∈
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) := by
    exact hadj.2.2.1
  rcases
      sourceLocalLayerSerialCellRebase_activeTarget_mem_switch_or_currentCell
        graphData minimal caps coloring web corridor hunique offset hnext
          targetEdge hregion with hswitch | hcell
  · apply Finset.mem_union_right _
    apply sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar
      corridor hunique offset hnext
    change web.annular.RS.edgeOf dart ∈
      sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext at hswitch
    simpa using hswitch
  · apply Finset.mem_union_left _
    apply Finset.mem_union_left _
    exact (mem_dartsOnEdges_iff web.annular.RS _ dart).2 hcell

/-- Partial coordinate map from the actual-cardinality next facial carrier to
the uniform forty-eight-dart carrier. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext)
    let uniform := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      corridor hunique offset hnext
    Fin target.card → Option (Fin uniform.card) := by
  classical
  dsimp only
  let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext)
  let uniform := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  intro targetSlot
  let dart := ((carrierCoordinate target).symm targetSlot).1
  if hdart : dart ∈ uniform then
    exact some (carrierCoordinate uniform ⟨dart, hdart⟩)
  else
    exact none

/-- Every mapped target coordinate denotes the same ambient dart. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt_dart_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (targetSlot : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).card)
    (uniformSlot : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        offset hnext).card)
    (hsource :
      sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt corridor hunique
        offset hnext targetSlot = some uniformSlot) :
    sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique offset
        hnext uniformSlot =
      (((carrierCoordinate
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))).symm targetSlot).1) := by
  classical
  simp only [sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt,
    id_eq] at hsource
  split at hsource <;> rename_i hdart
  · simp only [Option.some.injEq] at hsource
    subst uniformSlot
    simp [sourceLocalLayerSerialCellRebaseUniformFaceDartAt]
  · cases hsource

/-- An unmapped target coordinate is inactive in the literal successor facial
graph. -/
theorem
    sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt_none_not_mem_support
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
    (targetSlot : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).card)
    (hnone :
      sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt corridor hunique
        offset hnext targetSlot = none) :
    (((carrierCoordinate
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext))).symm targetSlot).1) ∉
      (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique offset
        hnext).support := by
  classical
  let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext)
  let targetDart : {dart // dart ∈ target} :=
    (carrierCoordinate target).symm targetSlot
  have hnotUniform : targetDart.1 ∉
      sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        offset hnext := by
    simp only [sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt,
      id_eq] at hnone
    split at hnone <;> rename_i hdart
    · cases hnone
    · exact hdart
  intro hsupport
  exact hnotUniform
    (sourceLocalLayerSerialCellRebase_activeFaceTarget_mem_uniform graphData
      minimal caps coloring web corridor hunique offset hnext targetDart.1
        targetDart.2 hsupport)

/-- Exact successor exterior code after contraction to the literal next
rolling facial carrier. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFaceTargetRawCodeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    BoundedInterfaceExteriorCode (Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).card) :=
  partialContractedInterfaceExteriorCode
    (sourceLocalLayerSerialCellRebaseUniformFaceSuccessorRawCodeAt corridor
      hunique offset hnext)
    (sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt corridor hunique
      offset hnext)

/-- The contracted code is the canonical exact successor facial code on the
actual-cardinality next rolling carrier. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceTargetRawCodeAt_exact
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
    let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext)
    let targetDart := fun slot : Fin target.card =>
      ((carrierCoordinate target).symm slot).1
    sourceLocalLayerSerialCellRebaseUniformFaceTargetRawCodeAt corridor hunique
        offset hnext =
      exactInterfaceExteriorCode
        (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique
          offset hnext) targetDart := by
  dsimp only
  let graph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
    hunique offset hnext
  let largerDart := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext)
  let targetDart := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let retain := sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt
    corridor hunique offset hnext
  have hcode :=
    sourceLocalLayerSerialCellRebaseUniformFaceSuccessorCodeAt_exact corridor
      hunique offset hnext
  change partialContractedInterfaceExteriorCode
      (sourceLocalLayerSerialCellRebaseUniformFaceSuccessorRawCodeAt corridor
        hunique offset hnext) retain =
      exactInterfaceExteriorCode graph targetDart
  rw [hcode]
  have hinjective : Function.Injective targetDart := by
    intro left right heq
    apply (carrierCoordinate target).symm.injective
    exact Subtype.ext heq
  have hsome : ∀ retained slot, retain retained = some slot →
      largerDart slot = targetDart retained := by
    intro retained slot hretain
    exact sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt_dart_eq
      corridor hunique offset hnext retained slot hretain
  have hnone : ∀ retained, retain retained = none →
      targetDart retained ∉ graph.support := by
    intro retained hretain
    exact
      sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt_none_not_mem_support
        graphData minimal caps coloring web corridor hunique offset hnext
          retained hretain
  apply boundedInterfaceExteriorCode_ext_iff
  · intro left right
    change partialReindexedVertexEq left right = true ↔
      (exactInterfaceExteriorCode graph targetDart).vertexEq left right = true
    rw [partialReindexedVertexEq_eq_true_iff targetDart hinjective]
    simp [exactInterfaceExteriorCode]
  · intro left right
    change partialReindexedDirectAdj
        (exactInterfaceExteriorCode graph largerDart) retain left right = true ↔
      (exactInterfaceExteriorCode graph targetDart).directAdj left right = true
    rw [partialReindexedDirectAdj_exact_iff graph largerDart targetDart retain
      hsome hnone left right]
    simp [exactInterfaceExteriorCode]
  · intro left right
    change partialReindexedExteriorConnected
        (exactInterfaceExteriorCode graph largerDart) retain left right = true ↔
      (exactInterfaceExteriorCode graph targetDart).exteriorConnected left
        right = true
    rw [partialReindexedExteriorConnected_exact_eq_true_iff graph largerDart
      targetDart retain hsome hnone left right]
    simp [exactInterfaceExteriorCode]

end

end GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCode

end Mettapedia.GraphTheory.FourColor
