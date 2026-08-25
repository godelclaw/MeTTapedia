import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformInterface
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorMaskUpdate
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorTotal

/-!
# Exact facial recurrence on the uniform Cell--rebase interface

The cumulative facial graph immediately before a boundary rebase may contain
arbitrarily much prefix history.  The bounded-interface theorem nevertheless
places every dart occurrence touched by one literal Cell and its following
rebase in a carrier of at most forty-eight darts.

This file transports the cumulative facial update through that fixed carrier.
It extracts the exact exterior-component code of the pre-rebase facial graph,
deletes precisely the darts over the four switch edges, and adds the canonical
local successor residual.  The resulting finite code is proved rowwise equal
to the exact code of the literal successor face graph.  Thus its total closure
computes successor facial reachability between every pair of named darts.

This is the facial analogue of the forty-nine-edge tracked recurrence.  It
does not yet combine the two recurrences with the remaining Cell-letter fields
or enumerate realizable initial states.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorMaskUpdate
open GoertzelV24InterfaceDeletionComponentFactorTotal
open GoertzelV24InterfaceDeletionComponentFactorUpdate
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellUniformFaceRecurrenceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance cellUniformFaceRecurrenceOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The ambient dart represented by one coordinate of the uniform facial
interaction carrier. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFaceDartAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Fin (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
      hunique offset hnext).card → web.annular.RS.D :=
  fun slot =>
    ((carrierCoordinate
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext)).symm slot).1

/-- Uniform facial coordinates name distinct ambient darts. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Function.Injective
      (sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique offset
        hnext) := by
  intro left right heq
  apply (carrierCoordinate
    (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
      offset hnext)).symm.injective
  apply Subtype.ext
  exact heq

/-- Every dart over a switch edge belongs to the uniform facial carrier. -/
theorem sourceLocalLayerBoundaryRebaseChangedFaceDarts_subset_uniformFaceCarrier
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    sourceLocalLayerBoundaryRebaseChangedFaceDartsAt corridor hunique offset
        hnext ⊆
      sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        offset hnext := by
  intro dart hdart
  exact Finset.mem_union_right _
    (sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar corridor
      hunique offset hnext hdart)

/-- The Boolean deletion mask selects precisely the dart occurrences over the
literal four-edge switch. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Fin (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
      hunique offset hnext).card → Bool :=
  fun slot => decide
    (web.annular.RS.edgeOf
        (sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique
          offset hnext slot) ∈
      sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext)

/-- A dart is selected by the coordinate mask exactly when its underlying edge
belongs to the source switch. -/
theorem removedBy_uniformFaceSwitchMask_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (dart : web.annular.RS.D) :
    RemovedByInterfaceMask
        (sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique
          offset hnext)
        (sourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt corridor hunique
          offset hnext) dart ↔
      web.annular.RS.edgeOf dart ∈
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext := by
  let carrier :=
    sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
      offset hnext
  let dartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  let removed := sourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt
    corridor hunique offset hnext
  constructor
  · rintro ⟨slot, hremoved, rfl⟩
    simpa [removed, sourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt]
      using hremoved
  · intro hdart
    have hchanged : dart ∈
        sourceLocalLayerBoundaryRebaseChangedFaceDartsAt corridor hunique offset
          hnext := by
      simpa using hdart
    have hcarrier : dart ∈ carrier :=
      sourceLocalLayerBoundaryRebaseChangedFaceDarts_subset_uniformFaceCarrier
        corridor hunique offset hnext hchanged
    let slot : Fin carrier.card := carrierCoordinate carrier ⟨dart, hcarrier⟩
    have hdartAt :
        sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique
          offset hnext slot = dart := by
      simp [sourceLocalLayerSerialCellRebaseUniformFaceDartAt, slot, carrier]
    refine ⟨slot, ?_, ?_⟩
    · change decide
        (web.annular.RS.edgeOf
            (sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique
              offset hnext slot) ∈
          sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext) =
        true
      rw [hdartAt]
      exact decide_eq_true hdart
    · exact hdartAt.symm

/-- Masking the switch occurrences in the cumulative pre-rebase facial graph
gives exactly the unchanged facial core. -/
theorem restrictedPreRebaseFaceGraph_uniformSwitchMask_eq_core
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    let graph := faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    restrictedByMask graph
        (sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique offset
          hnext)
        (sourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt corridor hunique
          offset hnext) =
      sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique offset
        hnext := by
  dsimp only
  let graph := faceRegionalDartGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
  let dartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  let removed := sourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt
    corridor hunique offset hnext
  have hsurvives :
      survivesMask dartAt removed = fun dart =>
        web.annular.RS.edgeOf dart ∉
          sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext := by
    funext dart
    apply propext
    rw [survivesMask_iff_not_removedByInterfaceMask]
    rw [removedBy_uniformFaceSwitchMask_iff corridor hunique offset hnext dart]
  rw [restrictedByMask, hsurvives]
  ext left right
  simp only [supportRestriction_adj,
    sourceLocalLayerBoundaryRebaseCoreFaceGraphAt, faceRegionalDartGraph_adj,
    sourceLocalLayerBoundaryRebaseFaceCoreRegionAt, Finset.mem_sdiff]
  tauto

/-- The executable facial row update on the literal uniform carrier: mask the
switch occurrences of the exact cumulative code, then add the local successor
facial adjacency row. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFaceSuccessorRawCodeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    BoundedInterfaceExteriorCode
      (Fin (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext).card) :=
  let dartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  let removed := sourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt
    corridor hunique offset hnext
  let preRebase := faceRegionalDartGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
  let localGraph := sourceLocalLayerBoundaryRebaseLocalFaceGraphAt corridor
    hunique offset hnext
  addInterfaceAdjacency
    (maskInterfaceExteriorCode
      (exactInterfaceExteriorCode preRebase dartAt) removed)
    (fun left right => by
      classical
      exact decide (localGraph.Adj (dartAt left) (dartAt right)))

/-- Closed source-independent packaging of the exact facial update.  The
dependent coordinate count is stored below the uniform bound of forty-eight. -/
noncomputable def
    sourceLocalLayerSerialCellRebaseUniformFaceBoundedSuccessorCodeAt
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
    BoundedInterfaceExteriorFamilyCode 48 Unit := by
  let carrier :=
    sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
      offset hnext
  have hcard : carrier.card ≤ 48 :=
    sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt_card_le_fortyEight
      graphData minimal caps coloring web corridor hunique offset hnext
  exact {
    vertexCount := ⟨carrier.card, Nat.lt_succ_of_le hcard⟩
    code := fun _ =>
      sourceLocalLayerSerialCellRebaseUniformFaceSuccessorRawCodeAt corridor
        hunique offset hnext }

/-- The finite facial row update is exactly the mask-independent exterior code
of the literal successor face graph. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceSuccessorCodeAt_exact
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    let dartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
      hunique offset hnext
    sourceLocalLayerSerialCellRebaseUniformFaceSuccessorRawCodeAt corridor
        hunique offset hnext =
      exactInterfaceExteriorCode
        (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique
          offset hnext) dartAt := by
  dsimp only
  let carrier :=
    sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
      offset hnext
  let dartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  let removed := sourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt
    corridor hunique offset hnext
  let preRebase := faceRegionalDartGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
  let coreGraph := sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique
    offset hnext
  let localGraph := sourceLocalLayerBoundaryRebaseLocalFaceGraphAt corridor
    hunique offset hnext
  have hinjective : Function.Injective dartAt :=
    sourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective corridor hunique
      offset hnext
  have hlocalSupport : localGraph.support ⊆ Set.range dartAt := by
    intro dart hdart
    have hcarrier : dart ∈ carrier :=
      (sourceLocalLayerSerialCell_faceRebase_support_subset_uniformInterface
        corridor hunique offset hnext).2 hdart
    refine ⟨carrierCoordinate carrier ⟨dart, hcarrier⟩, ?_⟩
    simp [dartAt, sourceLocalLayerSerialCellRebaseUniformFaceDartAt, carrier]
  change
    addInterfaceAdjacency
        (maskInterfaceExteriorCode
          (exactInterfaceExteriorCode preRebase dartAt) removed)
        (fun left right => by
          classical
          exact decide (localGraph.Adj (dartAt left) (dartAt right))) =
      exactInterfaceExteriorCode
        (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique
          offset hnext) dartAt
  rw [maskInterfaceExteriorCode_exact_code_eq preRebase dartAt hinjective
    removed]
  rw [restrictedPreRebaseFaceGraph_uniformSwitchMask_eq_core corridor hunique
    offset hnext]
  have hadded :
      addInterfaceAdjacency
          (exactInterfaceExteriorCode coreGraph dartAt)
          (fun left right => by
            classical
            exact decide (localGraph.Adj (dartAt left) (dartAt right))) =
        exactInterfaceExteriorCode (coreGraph ⊔ localGraph) dartAt := by
    apply addInterfaceAdjacency_exact_code_eq coreGraph localGraph dartAt
      hlocalSupport
    intro left right
    simp
  rw [hadded]
  exact congrArg (fun graph => exactInterfaceExteriorCode graph dartAt)
    (sourceLocalLayerBoundaryRebaseCore_sup_local_eq_successor corridor hunique
      offset hnext)

/-- The closed finite facial code computes literal successor reachability
between all named uniform dart coordinates. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceSuccessorCodeAt_reachable_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        offset hnext).card) :
    let dartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
      hunique offset hnext
    InterfaceExteriorTotalFactoredReachability
        (sourceLocalLayerSerialCellRebaseUniformFaceSuccessorRawCodeAt corridor
          hunique offset hnext)
        dartAt (fun _ => false) left right ↔
      (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique
        offset hnext).Reachable (dartAt left) (dartAt right) := by
  dsimp only
  rw [sourceLocalLayerSerialCellRebaseUniformFaceSuccessorCodeAt_exact corridor
    hunique offset hnext]
  rw [exactInterfaceExteriorCode_totalFactoredReachability_iff]
  have hrestricted :
      restrictedByMask
          (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique
            offset hnext)
          (sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique
            offset hnext)
          (fun _ => false) =
        sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique
          offset hnext := by
    rw [restrictedByMask]
    have hkeep :
        survivesMask
            (sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique
              offset hnext)
            (fun _ => false) =
          (fun _ => True) := by
      funext dart
      apply propext
      simp [survivesMask]
    rw [hkeep]
    exact supportRestriction_true _
  rw [hrestricted]

end

end GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence

end Mettapedia.GraphTheory.FourColor
