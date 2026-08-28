import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceRollingLocality
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingSuccessor

/-!
# Finite selected facial rolling successor

This module instantiates the graph-free forty-eight-dart rolling ABI on the
corrected pointwise-selected Cell carriers.  The factor stores only bounded
coordinates and incidence addresses; selected facial locality proves that
every active following coordinate is addressable by the present receipt.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedFaceRollingSuccessor

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24ClosedWebPointwiseSelectedFaceRollingLocality
open GoertzelV24ClosedWebPointwiseSelectedFaceSuccessor
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetCap
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetCode
open GoertzelV24ClosedWebPointwiseSelectedFaceUniformRecurrence
open GoertzelV24ClosedWebPointwiseSelectedRootedInteractionState
open GoertzelV24CorridorProfile
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorForget
open GoertzelV24InterfaceDeletionComponentFactorForgetExterior
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFactorForget
open GoertzelV24InterfaceExteriorLabelCapFactorForgetExact
open GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellCarrier
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFaceRollingSuccessorOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Direction-sensitive finite address of one following-interaction facial
incidence.  A live exterior endpoint is named directly when retained; otherwise
the active target dart supplies the oriented old incidence. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (incidence : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card × Bool) :
    Option (ExteriorLabelCapContractionAtom
      (Fin (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
        hinterior offset hnext).card)
      (Fin (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
        hinterior offset hnext).card × Bool)) := by
  classical
  let graph := pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
    hinterior offset hnext
  let current := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    web.toFormation corridor hinterior offset hnext
  let target := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext) hnextNext
  let currentDartAt := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
    web.toFormation corridor hinterior offset hnext
  let targetDartAt := fun slot : Fin target.card ↦
    ((carrierCoordinate target).symm slot).1
  let outside := faceInterfaceIncidenceVertex web.annular.RS targetDartAt
    incidence
  if hpresent : ExteriorIncidencePresent graph targetDartAt Prod.fst
      (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) incidence then
    if houtsideCurrent : outside ∈ current then
      exact some (.inl (carrierCoordinate current ⟨outside, houtsideCurrent⟩))
    else
      have htargetSupport : targetDartAt incidence.1 ∈ graph.support :=
        (SimpleGraph.mem_support graph).2 ⟨outside, hpresent.2⟩
      have htargetCurrent : targetDartAt incidence.1 ∈ current :=
        pointwiseSelectedSourceLocalLayerSerialCellRebase_activeNextFaceInteraction_mem_currentFaceInteraction
          graphData minimal caps coloring web corridor hinterior offset hnext
            hnextNext (targetDartAt incidence.1)
            ((carrierCoordinate target).symm incidence.1).2 htargetSupport
      exact some (.inr
        (carrierCoordinate current ⟨targetDartAt incidence.1, htargetCurrent⟩,
          incidence.2))
  else
    exact none

/-- Literal finite facial rolling factor for two consecutive Cell--rebase
positions. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3) :
    SourceLocalLayerSerialFaceRollingFactor := by
  classical
  let hcell :=
    pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData minimal
      caps coloring web corridor hinterior offset
  let rebase := pointwiseSelectedSourceLocalLayerSerialFaceRebaseFactorAt
    graphData minimal caps coloring web corridor hinterior offset hnext hcell
  let current := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    web.toFormation corridor hinterior offset hnext
  let next := sourceLocalLayerNextOffset offset hnext
  let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
    next
  let nextInteraction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
      next hnextNext
  let nextRegion := pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
    next
  let nextDartAt := fun slot : Fin nextInteraction.card ↦
    ((carrierCoordinate nextInteraction).symm slot).1
  let hcellNext :=
    pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData minimal
      caps coloring web corridor hinterior next
  have hnextInteraction : nextInteraction.card ≤ 48 :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt_card_le_fortyEight
      web.toFormation corridor hinterior next hnextNext hcellNext
  exact {
    rebase := rebase
    nextInteractionCount :=
      ⟨nextInteraction.card, Nat.lt_succ_of_le hnextInteraction⟩
    nextInteractionSource := finiteCarrierPartialSource current nextInteraction
    nextInteractionPresent := fun slot ↦ by
      exact decide (web.annular.RS.edgeOf (nextDartAt slot) ∈ nextRegion)
    nextInteractionEntry := pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt graphData
      minimal caps coloring web corridor hinterior offset hnext hnextNext
    nextCurrentCoordinate := fun targetSlot ↦
      carrierCoordinate nextInteraction
        ⟨((carrierCoordinate target).symm targetSlot).1,
          Finset.mem_union_left _ ((carrierCoordinate target).symm
            targetSlot).2⟩ }

@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt_nextInteractionCount
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3) :
    (pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt graphData minimal caps coloring
      web corridor hinterior offset hnext hnextNext).nextInteractionCount.val =
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card := by
  rfl

/-- A mapped following-interaction coordinate denotes the same ambient dart. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt_nextInteractionSource_dart_eq
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (nextSlot : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card)
    (currentSlot : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
        offset hnext).card)
    (hsource :
      (pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt graphData minimal caps coloring
        web corridor hinterior offset hnext hnextNext
        ).nextInteractionSource nextSlot = some currentSlot) :
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt web.toFormation corridor hinterior offset
        hnext currentSlot =
      (((carrierCoordinate
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
          hinterior (sourceLocalLayerNextOffset offset hnext) hnextNext)
        ).symm nextSlot).1) := by
  let current := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    web.toFormation corridor hinterior offset hnext
  let nextInteraction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
      (sourceLocalLayerNextOffset offset hnext) hnextNext
  change finiteCarrierPartialSource current nextInteraction nextSlot =
    some currentSlot at hsource
  exact finiteCarrierPartialSource_eq_some_value_eq current nextInteraction
    nextSlot currentSlot hsource

/-- The rolling incidence decoder succeeds exactly on literal successor
incidences of the following interaction carrier. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_isSome_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (incidence : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card × Bool) :
    (pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt graphData minimal caps coloring
      web corridor hinterior offset hnext hnextNext incidence).isSome ↔
      let graph := pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
        hinterior offset hnext
      let target := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext) hnextNext
      let targetDartAt := fun slot : Fin target.card ↦
        ((carrierCoordinate target).symm slot).1
      ExteriorIncidencePresent graph targetDartAt Prod.fst
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
        incidence := by
  classical
  unfold pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt
  dsimp only
  split <;> rename_i hpresent
  · split
    · exact ⟨fun _ ↦ hpresent, fun _ ↦ rfl⟩
    · exact ⟨fun _ ↦ hpresent, fun _ ↦ rfl⟩
  · simp [hpresent]

/-- A left-branch rolling entry is literally the target incidence endpoint,
and no target coordinate is retained at that current slot. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_left
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (incidence : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card × Bool)
    (currentSlot : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
        offset hnext).card)
    (hentry : pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt graphData minimal caps
      coloring web corridor hinterior offset hnext hnextNext incidence =
        some (.inl currentSlot)) :
    let current := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      web.toFormation corridor hinterior offset hnext
    let target := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext) hnextNext
    let currentDartAt := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
      web.toFormation corridor hinterior offset hnext
    let targetDartAt := fun slot : Fin target.card ↦
      ((carrierCoordinate target).symm slot).1
    currentDartAt currentSlot =
        faceInterfaceIncidenceVertex web.annular.RS targetDartAt incidence ∧
      ∀ targetSlot,
        finiteCarrierPartialSource current target targetSlot ≠ some currentSlot := by
  classical
  dsimp only
  unfold pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt at hentry
  dsimp only at hentry
  split at hentry <;> rename_i hpresent
  · split at hentry <;> rename_i houtsideCurrent
    · simp only [Option.some.injEq, Sum.inl.injEq] at hentry
      subst currentSlot
      constructor
      · simp [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt]
      · intro targetSlot hsource
        let current := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
          web.toFormation corridor hinterior offset hnext
        let target := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
          web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext) hnextNext
        have hdart := finiteCarrierPartialSource_eq_some_value_eq current target
          targetSlot
          (carrierCoordinate current
            ⟨faceInterfaceIncidenceVertex web.annular.RS
                (fun slot : Fin target.card ↦
                  ((carrierCoordinate target).symm slot).1)
                incidence,
              houtsideCurrent⟩)
          hsource
        exact hpresent.1 targetSlot (by
          simpa [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt, current,
            target] using hdart)
    · cases hentry
  · cases hentry

/-- A right-branch rolling entry is the corresponding live strict-exterior
incidence of the current interaction carrier. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_right
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (incidence : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card × Bool)
    (currentIncidence : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
        offset hnext).card × Bool)
    (hentry : pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt graphData minimal caps
      coloring web corridor hinterior offset hnext hnextNext incidence =
        some (.inr currentIncidence)) :
    let graph := pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
      hinterior offset hnext
    let target := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext) hnextNext
    let currentDartAt := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
      web.toFormation corridor hinterior offset hnext
    let targetDartAt := fun slot : Fin target.card ↦
      ((carrierCoordinate target).symm slot).1
    faceInterfaceIncidenceVertex web.annular.RS currentDartAt currentIncidence =
        faceInterfaceIncidenceVertex web.annular.RS targetDartAt incidence ∧
      ExteriorIncidencePresent graph currentDartAt Prod.fst
        (faceInterfaceIncidenceVertex web.annular.RS currentDartAt)
        currentIncidence := by
  classical
  dsimp only
  unfold pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt at hentry
  dsimp only at hentry
  split at hentry <;> rename_i hpresent
  · split at hentry <;> rename_i houtsideCurrent
    · cases hentry
    · simp only [Option.some.injEq, Sum.inr.injEq] at hentry
      subst currentIncidence
      let current := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        web.toFormation corridor hinterior offset hnext
      let target := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext) hnextNext
      let currentDartAt := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
        web.toFormation corridor hinterior offset hnext
      let targetDartAt := fun slot : Fin target.card ↦
        ((carrierCoordinate target).symm slot).1
      have hbase : currentDartAt
          (carrierCoordinate current
            ⟨targetDartAt incidence.1,
              pointwiseSelectedSourceLocalLayerSerialCellRebase_activeNextFaceInteraction_mem_currentFaceInteraction
                graphData minimal caps coloring web corridor hinterior offset
                  hnext hnextNext (targetDartAt incidence.1)
                  ((carrierCoordinate target).symm incidence.1).2
                  ((SimpleGraph.mem_support
                    (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
                      hinterior offset hnext)).2
                    ⟨faceInterfaceIncidenceVertex web.annular.RS targetDartAt
                        incidence,
                      hpresent.2⟩)⟩) = targetDartAt incidence.1 := by
        simp [currentDartAt,
          pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt, current]
      have hvertex :
          faceInterfaceIncidenceVertex web.annular.RS currentDartAt
              (carrierCoordinate current
                ⟨targetDartAt incidence.1,
                  pointwiseSelectedSourceLocalLayerSerialCellRebase_activeNextFaceInteraction_mem_currentFaceInteraction
                    graphData minimal caps coloring web corridor hinterior offset
                      hnext hnextNext (targetDartAt incidence.1)
                      ((carrierCoordinate target).symm incidence.1).2
                      ((SimpleGraph.mem_support
                        (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
                          web.toFormation corridor hinterior offset hnext)).2
                        ⟨faceInterfaceIncidenceVertex web.annular.RS targetDartAt
                            incidence,
                          hpresent.2⟩)⟩,
                incidence.2) =
            faceInterfaceIncidenceVertex web.annular.RS targetDartAt
              incidence := by
        rcases incidence with ⟨slot, direction⟩
        cases direction <;> simp_all
      refine ⟨hvertex, ?_⟩
      unfold ExteriorIncidencePresent
      constructor
      · intro currentSlot heq
        apply houtsideCurrent
        have hmem : currentDartAt currentSlot ∈ current :=
          ((carrierCoordinate current).symm currentSlot).2
        have heq' :
            faceInterfaceIncidenceVertex web.annular.RS targetDartAt
                incidence = currentDartAt currentSlot :=
          hvertex.symm.trans heq
        rw [← heq'] at hmem
        exact hmem
      · change
          (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor hinterior
            offset hnext).Adj
              (currentDartAt
                (carrierCoordinate current ⟨targetDartAt incidence.1, _⟩))
              (faceInterfaceIncidenceVertex web.annular.RS currentDartAt
                (carrierCoordinate current ⟨targetDartAt incidence.1, _⟩,
                  incidence.2))
        rw [hbase, hvertex]
        exact hpresent.2
  · cases hentry

/-- Every decoded rolling incidence denotes a physically live contraction
atom of the exact uniform successor code. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_atomPresent
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (incidence : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card × Bool)
    (atom : ExteriorLabelCapContractionAtom
      (Fin (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
        hinterior offset hnext).card)
      (Fin (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
        hinterior offset hnext).card × Bool))
    (hentry : pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt graphData minimal caps
      coloring web corridor hinterior offset hnext hnextNext incidence =
        some atom) :
    exteriorLabelCapContractionAtomPresent
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
          web.toFormation corridor hinterior offset hnext)
        (finiteCarrierPartialSource
          (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
            hinterior offset hnext)
          (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
            hinterior (sourceLocalLayerNextOffset offset hnext) hnextNext))
        atom = true := by
  classical
  rw [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_exact
    web.toFormation corridor hinterior offset hnext]
  let graph := pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
    hinterior offset hnext
  let current := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    web.toFormation corridor hinterior offset hnext
  let target := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext) hnextNext
  let currentDartAt := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
    web.toFormation corridor hinterior offset hnext
  let targetDartAt := fun slot : Fin target.card ↦
    ((carrierCoordinate target).symm slot).1
  let retain := finiteCarrierPartialSource current target
  have hpresentTarget : ExteriorIncidencePresent graph targetDartAt Prod.fst
      (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) incidence :=
    (pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData minimal caps
      coloring web corridor hinterior offset hnext hnextNext incidence).1
      (by simp [hentry])
  cases atom with
  | inl currentSlot =>
      unfold exteriorLabelCapContractionAtomPresent
      have hleft := pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_left graphData
        minimal caps coloring web corridor hinterior offset hnext hnextNext
          incidence currentSlot hentry
      rcases hleft with ⟨hvertex, hnotRetained⟩
      simp only [Bool.and_eq_true]
      constructor
      · apply (exactFaceInterfaceExteriorLabelCapCode_interfacePresent_iff
          web.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
            (sourceLocalLayerNextOffset offset hnext))
          currentDartAt currentSlot 6).2
        have houtsideRegion : web.annular.RS.edgeOf
              (faceInterfaceIncidenceVertex web.annular.RS targetDartAt
                incidence) ∈
            pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
              (sourceLocalLayerNextOffset offset hnext) :=
          hpresentTarget.2.2.2.2
        simpa [currentDartAt, targetDartAt] using
          hvertex.symm ▸ houtsideRegion
      · apply (codeSurvivesPartialRetained_exact_iff graph currentDartAt retain
          currentSlot).2
        intro removedSlot hremoved heq
        rw [partialRetainedCoordinateMask_eq_true_iff] at hremoved
        rcases hremoved with ⟨targetSlot, hsource⟩
        have hslot : currentSlot = removedSlot :=
          (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective
            web.toFormation corridor hinterior offset hnext) heq
        subst removedSlot
        exact hnotRetained targetSlot hsource
  | inr currentIncidence =>
      unfold exteriorLabelCapContractionAtomPresent
      have hright := pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_right graphData
        minimal caps coloring web corridor hinterior offset hnext hnextNext
          incidence currentIncidence hentry
      exact (exactFaceInterfaceExteriorLabelCapCode_incidencePresent_iff
        web.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext))
        currentDartAt currentIncidence 6).2 hright.2

/-- A decoded rolling atom is the literal exterior endpoint of its target
incidence. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_atomVertex
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (incidence : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card × Bool)
    (atom : ExteriorLabelCapContractionAtom
      (Fin (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
        hinterior offset hnext).card)
      (Fin (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
        hinterior offset hnext).card × Bool))
    (hentry : pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt graphData minimal caps
      coloring web corridor hinterior offset hnext hnextNext incidence =
        some atom) :
    let target := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext) hnextNext
    let currentDartAt := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
      web.toFormation corridor hinterior offset hnext
    let targetDartAt := fun slot : Fin target.card ↦
      ((carrierCoordinate target).symm slot).1
    exteriorLabelCapContractionAtomVertex currentDartAt
        (faceInterfaceIncidenceVertex web.annular.RS currentDartAt) atom =
      faceInterfaceIncidenceVertex web.annular.RS targetDartAt incidence := by
  classical
  dsimp only
  cases atom with
  | inl currentSlot =>
      exact (pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_left graphData minimal
        caps coloring web corridor hinterior offset hnext hnextNext incidence
          currentSlot hentry).1
  | inr currentIncidence =>
      exact (pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_right graphData minimal
        caps coloring web corridor hinterior offset hnext hnextNext incidence
          currentIncidence hentry).1

/-- An unmapped following-interaction coordinate is inactive in the literal
successor facial graph. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt_nextInteractionSource_none_not_mem_support
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (nextSlot : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card)
    (hnone :
      (pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt graphData minimal caps coloring
        web corridor hinterior offset hnext hnextNext
        ).nextInteractionSource nextSlot = none) :
    (((carrierCoordinate
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext) hnextNext)).symm nextSlot).1) ∉
      (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor hinterior offset
        hnext).support := by
  classical
  let current := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    web.toFormation corridor hinterior offset hnext
  let nextInteraction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
      (sourceLocalLayerNextOffset offset hnext) hnextNext
  let targetDart : {dart // dart ∈ nextInteraction} :=
    (carrierCoordinate nextInteraction).symm nextSlot
  have hnotCurrent : targetDart.1 ∉ current := by
    change (finiteCarrierPartialSource current nextInteraction nextSlot = none)
      at hnone
    exact finiteCarrierPartialSource_eq_none_not_mem current nextInteraction
      nextSlot hnone
  intro hsupport
  exact hnotCurrent
    (pointwiseSelectedSourceLocalLayerSerialCellRebase_activeNextFaceInteraction_mem_currentFaceInteraction
      graphData minimal caps coloring web corridor hinterior offset hnext hnextNext
        targetDart.1 targetDart.2 hsupport)

/-- The finite rolling coordinate inclusion is the following rooted state's
facial current-coordinate field. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt_nextCurrentCoordinate_eq
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
        corridor hinterior (sourceLocalLayerNextOffset offset hnext) step) ≠ 0) :
    (pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt graphData minimal caps coloring
      web corridor hinterior offset hnext hnextNext).nextCurrentCoordinate =
      (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext)
          hnextNext
          (pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData
            minimal caps coloring web corridor hinterior
              (sourceLocalLayerNextOffset offset hnext))
          color hcrossing
        ).faceCurrentCoordinate := by
  rfl

end

end GoertzelV24ClosedWebPointwiseSelectedFaceRollingSuccessor

end Mettapedia.GraphTheory.FourColor
