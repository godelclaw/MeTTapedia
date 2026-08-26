import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingLocality
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingSuccessor

/-!
# Finite rolling successor for the rooted facial interaction code

The exact boundary rebase produces a cap-six facial code on the current
forty-eight-dart interaction carrier.  Facial rolling locality proves that
every active dart of the following interaction carrier is already named there.
This file packages the partial coordinate map, literal activity, exterior
incidence addresses, and the inclusion of the following current carrier as one
finite factor.

The factor contains only bounded coordinates and addresses into the exact
uniform successor code.  It does not carry a precomputed successor profile.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingSuccessor

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCap
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCode
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingLocality
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
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
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Canonical executable order on oriented finite incidences. -/
local instance faceRollingSuccessorIncidenceLinearOrder {n : Nat} :
    LinearOrder (Fin n × Bool) :=
  LinearOrder.lift' (fun incidence : Fin n × Bool => toLex incidence)
    toLex.injective

local instance faceRollingSuccessorOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The exact facial rebase factor together with the finite contraction onto
the following interaction carrier and the inclusion of its current carrier. -/
structure SourceLocalLayerSerialFaceRollingFactor where
  rebase : SourceLocalLayerSerialFaceRebaseFactor
  nextInteractionCount : Fin 49
  nextInteractionSource :
    Fin nextInteractionCount.val → Option (Fin rebase.interactionCount.val)
  nextInteractionPresent : Fin nextInteractionCount.val → Bool
  nextInteractionEntry :
    Fin nextInteractionCount.val × Bool →
      Option (ExteriorLabelCapContractionAtom
        (Fin rebase.interactionCount.val)
        (Fin rebase.interactionCount.val × Bool))
  nextCurrentCoordinate :
    Fin rebase.targetCount.val → Fin nextInteractionCount.val

noncomputable instance : DecidableEq SourceLocalLayerSerialFaceRollingFactor :=
  Classical.decEq _

private abbrev sourceLocalLayerSerialFaceRollingFactorCode :=
  Σ rebase : SourceLocalLayerSerialFaceRebaseFactor,
    Σ nextInteractionCount : Fin 49,
      (Fin nextInteractionCount.val →
          Option (Fin rebase.interactionCount.val)) ×
        (Fin nextInteractionCount.val → Bool) ×
        (Fin nextInteractionCount.val × Bool →
          Option (ExteriorLabelCapContractionAtom
            (Fin rebase.interactionCount.val)
            (Fin rebase.interactionCount.val × Bool))) ×
        (Fin rebase.targetCount.val → Fin nextInteractionCount.val)

private def sourceLocalLayerSerialFaceRollingFactorEquiv :
    SourceLocalLayerSerialFaceRollingFactor ≃
      sourceLocalLayerSerialFaceRollingFactorCode where
  toFun factor := ⟨factor.rebase, factor.nextInteractionCount,
    factor.nextInteractionSource, factor.nextInteractionPresent,
    factor.nextInteractionEntry, factor.nextCurrentCoordinate⟩
  invFun factor := {
    rebase := factor.1
    nextInteractionCount := factor.2.1
    nextInteractionSource := factor.2.2.1
    nextInteractionPresent := factor.2.2.2.1
    nextInteractionEntry := factor.2.2.2.2.1
    nextCurrentCoordinate := factor.2.2.2.2.2 }
  left_inv factor := by cases factor; rfl
  right_inv factor := by
    rcases factor with ⟨rebase, nextCount, source, present, entry, coordinate⟩
    rfl

set_option synthInstance.maxSize 512 in
deriving noncomputable instance Fintype for
  sourceLocalLayerSerialFaceRollingFactorCode

noncomputable instance : Fintype SourceLocalLayerSerialFaceRollingFactor :=
  Fintype.ofEquiv _ sourceLocalLayerSerialFaceRollingFactorEquiv.symm

/-- Contract the exact uniform facial successor onto the following interaction
carrier. -/
def SourceLocalLayerSerialFaceRollingFactor.nextInteractionState
    (factor : SourceLocalLayerSerialFaceRollingFactor)
    (preRebase : SourceLocalLayerSerialFaceInteractionPrefixState)
    (hcount : preRebase.vertexCount = factor.rebase.interactionCount) :
    SourceLocalLayerSerialFaceInteractionPrefixState where
  vertexCount := factor.nextInteractionCount
  code := fun _ ↦ partialContractedInterfaceExteriorLabelCapCode
    (factor.rebase.uniformSuccessorCode preRebase hcount)
    factor.nextInteractionSource Prod.fst factor.nextInteractionPresent
    factor.nextInteractionEntry

/-- Guarded executable form of the facial rolling contraction. -/
def SourceLocalLayerSerialFaceRollingFactor.nextInteractionState?
    (factor : SourceLocalLayerSerialFaceRollingFactor)
    (preRebase : SourceLocalLayerSerialFaceInteractionPrefixState) :
    Option SourceLocalLayerSerialFaceInteractionPrefixState :=
  if hcount : preRebase.vertexCount = factor.rebase.interactionCount then
    some (factor.nextInteractionState preRebase hcount)
  else none

/-- Direction-sensitive finite address of one following-interaction facial
incidence.  A live exterior endpoint is named directly when retained; otherwise
the active target dart supplies the oriented old incidence. -/
noncomputable def sourceLocalLayerSerialFaceRollingEntryAt
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (incidence : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card × Bool) :
    Option (ExteriorLabelCapContractionAtom
      (Fin (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext).card)
      (Fin (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext).card × Bool)) := by
  classical
  let graph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
    hunique offset hnext
  let current := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let target := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique (sourceLocalLayerNextOffset offset hnext) hnextNext
  let currentDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt
    corridor hunique offset hnext
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
        sourceLocalLayerSerialCellRebase_activeNextFaceInteraction_mem_currentFaceInteraction
          graphData minimal caps coloring web corridor hunique offset hnext
            hnextNext (targetDartAt incidence.1)
            ((carrierCoordinate target).symm incidence.1).2 htargetSupport
      exact some (.inr
        (carrierCoordinate current ⟨targetDartAt incidence.1, htargetCurrent⟩,
          incidence.2))
  else
    exact none

/-- Literal finite facial rolling factor for two consecutive Cell--rebase
positions. -/
noncomputable def sourceLocalLayerSerialFaceRollingFactorAt
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3) :
    SourceLocalLayerSerialFaceRollingFactor := by
  classical
  let rebase := sourceLocalLayerSerialFaceRebaseFactorAt graphData minimal caps
    coloring web corridor hunique offset hnext
  let current := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let next := sourceLocalLayerNextOffset offset hnext
  let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    next
  let nextInteraction :=
    sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
      next hnextNext
  let nextRegion := sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
    next
  let nextDartAt := fun slot : Fin nextInteraction.card ↦
    ((carrierCoordinate nextInteraction).symm slot).1
  have hnextInteraction : nextInteraction.card ≤ 48 :=
    sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt_card_le_fortyEight
      graphData minimal caps coloring web corridor hunique next hnextNext
  exact {
    rebase := rebase
    nextInteractionCount :=
      ⟨nextInteraction.card, Nat.lt_succ_of_le hnextInteraction⟩
    nextInteractionSource := finiteCarrierPartialSource current nextInteraction
    nextInteractionPresent := fun slot ↦ by
      exact decide (web.annular.RS.edgeOf (nextDartAt slot) ∈ nextRegion)
    nextInteractionEntry := sourceLocalLayerSerialFaceRollingEntryAt graphData
      minimal caps coloring web corridor hunique offset hnext hnextNext
    nextCurrentCoordinate := fun targetSlot ↦
      carrierCoordinate nextInteraction
        ⟨((carrierCoordinate target).symm targetSlot).1,
          Finset.mem_union_left _ ((carrierCoordinate target).symm
            targetSlot).2⟩ }

@[simp]
theorem sourceLocalLayerSerialFaceRollingFactorAt_nextInteractionCount
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3) :
    (sourceLocalLayerSerialFaceRollingFactorAt graphData minimal caps coloring
      web corridor hunique offset hnext hnextNext).nextInteractionCount.val =
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card := by
  rfl

/-- A mapped following-interaction coordinate denotes the same ambient dart. -/
theorem sourceLocalLayerSerialFaceRollingFactorAt_nextInteractionSource_dart_eq
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (nextSlot : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card)
    (currentSlot : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        offset hnext).card)
    (hsource :
      (sourceLocalLayerSerialFaceRollingFactorAt graphData minimal caps coloring
        web corridor hunique offset hnext hnextNext
        ).nextInteractionSource nextSlot = some currentSlot) :
    sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique offset
        hnext currentSlot =
      (((carrierCoordinate
        (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
          hunique (sourceLocalLayerNextOffset offset hnext) hnextNext)
        ).symm nextSlot).1) := by
  let current := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let nextInteraction :=
    sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext) hnextNext
  change finiteCarrierPartialSource current nextInteraction nextSlot =
    some currentSlot at hsource
  exact finiteCarrierPartialSource_eq_some_value_eq current nextInteraction
    nextSlot currentSlot hsource

/-- The rolling incidence decoder succeeds exactly on literal successor
incidences of the following interaction carrier. -/
theorem sourceLocalLayerSerialFaceRollingEntryAt_isSome_iff
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (incidence : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card × Bool) :
    (sourceLocalLayerSerialFaceRollingEntryAt graphData minimal caps coloring
      web corridor hunique offset hnext hnextNext incidence).isSome ↔
      let graph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
        hunique offset hnext
      let target := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        corridor hunique (sourceLocalLayerNextOffset offset hnext) hnextNext
      let targetDartAt := fun slot : Fin target.card ↦
        ((carrierCoordinate target).symm slot).1
      ExteriorIncidencePresent graph targetDartAt Prod.fst
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
        incidence := by
  classical
  unfold sourceLocalLayerSerialFaceRollingEntryAt
  dsimp only
  split <;> rename_i hpresent
  · split
    · exact ⟨fun _ ↦ hpresent, fun _ ↦ rfl⟩
    · exact ⟨fun _ ↦ hpresent, fun _ ↦ rfl⟩
  · simp [hpresent]

/-- A left-branch rolling entry is literally the target incidence endpoint,
and no target coordinate is retained at that current slot. -/
theorem sourceLocalLayerSerialFaceRollingEntryAt_left
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (incidence : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card × Bool)
    (currentSlot : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        offset hnext).card)
    (hentry : sourceLocalLayerSerialFaceRollingEntryAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext incidence =
        some (.inl currentSlot)) :
    let current := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      corridor hunique offset hnext
    let target := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      corridor hunique (sourceLocalLayerNextOffset offset hnext) hnextNext
    let currentDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt
      corridor hunique offset hnext
    let targetDartAt := fun slot : Fin target.card ↦
      ((carrierCoordinate target).symm slot).1
    currentDartAt currentSlot =
        faceInterfaceIncidenceVertex web.annular.RS targetDartAt incidence ∧
      ∀ targetSlot,
        finiteCarrierPartialSource current target targetSlot ≠ some currentSlot := by
  classical
  dsimp only
  unfold sourceLocalLayerSerialFaceRollingEntryAt at hentry
  dsimp only at hentry
  split at hentry <;> rename_i hpresent
  · split at hentry <;> rename_i houtsideCurrent
    · simp only [Option.some.injEq, Sum.inl.injEq] at hentry
      subst currentSlot
      constructor
      · simp [sourceLocalLayerSerialCellRebaseUniformFaceDartAt]
      · intro targetSlot hsource
        let current := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
          corridor hunique offset hnext
        let target := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
          corridor hunique (sourceLocalLayerNextOffset offset hnext) hnextNext
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
          simpa [sourceLocalLayerSerialCellRebaseUniformFaceDartAt, current,
            target] using hdart)
    · cases hentry
  · cases hentry

/-- A right-branch rolling entry is the corresponding live strict-exterior
incidence of the current interaction carrier. -/
theorem sourceLocalLayerSerialFaceRollingEntryAt_right
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (incidence : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card × Bool)
    (currentIncidence : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        offset hnext).card × Bool)
    (hentry : sourceLocalLayerSerialFaceRollingEntryAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext incidence =
        some (.inr currentIncidence)) :
    let graph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
      hunique offset hnext
    let target := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      corridor hunique (sourceLocalLayerNextOffset offset hnext) hnextNext
    let currentDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt
      corridor hunique offset hnext
    let targetDartAt := fun slot : Fin target.card ↦
      ((carrierCoordinate target).symm slot).1
    faceInterfaceIncidenceVertex web.annular.RS currentDartAt currentIncidence =
        faceInterfaceIncidenceVertex web.annular.RS targetDartAt incidence ∧
      ExteriorIncidencePresent graph currentDartAt Prod.fst
        (faceInterfaceIncidenceVertex web.annular.RS currentDartAt)
        currentIncidence := by
  classical
  dsimp only
  unfold sourceLocalLayerSerialFaceRollingEntryAt at hentry
  dsimp only at hentry
  split at hentry <;> rename_i hpresent
  · split at hentry <;> rename_i houtsideCurrent
    · cases hentry
    · simp only [Option.some.injEq, Sum.inr.injEq] at hentry
      subst currentIncidence
      let current := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        corridor hunique offset hnext
      let target := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        corridor hunique (sourceLocalLayerNextOffset offset hnext) hnextNext
      let currentDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt
        corridor hunique offset hnext
      let targetDartAt := fun slot : Fin target.card ↦
        ((carrierCoordinate target).symm slot).1
      have hbase : currentDartAt
          (carrierCoordinate current
            ⟨targetDartAt incidence.1,
              sourceLocalLayerSerialCellRebase_activeNextFaceInteraction_mem_currentFaceInteraction
                graphData minimal caps coloring web corridor hunique offset
                  hnext hnextNext (targetDartAt incidence.1)
                  ((carrierCoordinate target).symm incidence.1).2
                  ((SimpleGraph.mem_support
                    (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
                      hunique offset hnext)).2
                    ⟨faceInterfaceIncidenceVertex web.annular.RS targetDartAt
                        incidence,
                      hpresent.2⟩)⟩) = targetDartAt incidence.1 := by
        simp [currentDartAt,
          sourceLocalLayerSerialCellRebaseUniformFaceDartAt, current]
      have hvertex :
          faceInterfaceIncidenceVertex web.annular.RS currentDartAt
              (carrierCoordinate current
                ⟨targetDartAt incidence.1,
                  sourceLocalLayerSerialCellRebase_activeNextFaceInteraction_mem_currentFaceInteraction
                    graphData minimal caps coloring web corridor hunique offset
                      hnext hnextNext (targetDartAt incidence.1)
                      ((carrierCoordinate target).symm incidence.1).2
                      ((SimpleGraph.mem_support
                        (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
                          corridor hunique offset hnext)).2
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
          (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique
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
theorem sourceLocalLayerSerialFaceRollingEntryAt_atomPresent
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (incidence : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card × Bool)
    (atom : ExteriorLabelCapContractionAtom
      (Fin (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext).card)
      (Fin (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext).card × Bool))
    (hentry : sourceLocalLayerSerialFaceRollingEntryAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext incidence =
        some atom) :
    exteriorLabelCapContractionAtomPresent
        (sourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
          corridor hunique offset hnext)
        (finiteCarrierPartialSource
          (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
            hunique offset hnext)
          (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
            hunique (sourceLocalLayerNextOffset offset hnext) hnextNext))
        atom = true := by
  classical
  let graph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
    hunique offset hnext
  let current := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let target := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique (sourceLocalLayerNextOffset offset hnext) hnextNext
  let currentDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt
    corridor hunique offset hnext
  let targetDartAt := fun slot : Fin target.card ↦
    ((carrierCoordinate target).symm slot).1
  let retain := finiteCarrierPartialSource current target
  have hpresentTarget : ExteriorIncidencePresent graph targetDartAt Prod.fst
      (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) incidence :=
    (sourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext incidence).1
      (by simp [hentry])
  cases atom with
  | inl currentSlot =>
      unfold exteriorLabelCapContractionAtomPresent
      have hleft := sourceLocalLayerSerialFaceRollingEntryAt_left graphData
        minimal caps coloring web corridor hunique offset hnext hnextNext
          incidence currentSlot hentry
      rcases hleft with ⟨hvertex, hnotRetained⟩
      simp only [Bool.and_eq_true]
      constructor
      · apply (exactFaceInterfaceExteriorLabelCapCode_interfacePresent_iff
          web.annular.RS
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext))
          currentDartAt currentSlot 6).2
        have houtsideRegion : web.annular.RS.edgeOf
              (faceInterfaceIncidenceVertex web.annular.RS targetDartAt
                incidence) ∈
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
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
          (sourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective corridor
            hunique offset hnext) heq
        subst removedSlot
        exact hnotRetained targetSlot hsource
  | inr currentIncidence =>
      unfold exteriorLabelCapContractionAtomPresent
      have hright := sourceLocalLayerSerialFaceRollingEntryAt_right graphData
        minimal caps coloring web corridor hunique offset hnext hnextNext
          incidence currentIncidence hentry
      exact (exactFaceInterfaceExteriorLabelCapCode_incidencePresent_iff
        web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))
        currentDartAt currentIncidence 6).2 hright.2

/-- A decoded rolling atom is the literal exterior endpoint of its target
incidence. -/
theorem sourceLocalLayerSerialFaceRollingEntryAt_atomVertex
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (incidence : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card × Bool)
    (atom : ExteriorLabelCapContractionAtom
      (Fin (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext).card)
      (Fin (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext).card × Bool))
    (hentry : sourceLocalLayerSerialFaceRollingEntryAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext incidence =
        some atom) :
    let target := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      corridor hunique (sourceLocalLayerNextOffset offset hnext) hnextNext
    let currentDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt
      corridor hunique offset hnext
    let targetDartAt := fun slot : Fin target.card ↦
      ((carrierCoordinate target).symm slot).1
    exteriorLabelCapContractionAtomVertex currentDartAt
        (faceInterfaceIncidenceVertex web.annular.RS currentDartAt) atom =
      faceInterfaceIncidenceVertex web.annular.RS targetDartAt incidence := by
  classical
  dsimp only
  cases atom with
  | inl currentSlot =>
      exact (sourceLocalLayerSerialFaceRollingEntryAt_left graphData minimal
        caps coloring web corridor hunique offset hnext hnextNext incidence
          currentSlot hentry).1
  | inr currentIncidence =>
      exact (sourceLocalLayerSerialFaceRollingEntryAt_right graphData minimal
        caps coloring web corridor hunique offset hnext hnextNext incidence
          currentIncidence hentry).1

/-- An unmapped following-interaction coordinate is inactive in the literal
successor facial graph. -/
theorem sourceLocalLayerSerialFaceRollingFactorAt_nextInteractionSource_none_not_mem_support
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (nextSlot : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card)
    (hnone :
      (sourceLocalLayerSerialFaceRollingFactorAt graphData minimal caps coloring
        web corridor hunique offset hnext hnextNext
        ).nextInteractionSource nextSlot = none) :
    (((carrierCoordinate
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) hnextNext)).symm nextSlot).1) ∉
      (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique offset
        hnext).support := by
  classical
  let current := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let nextInteraction :=
    sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
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
    (sourceLocalLayerSerialCellRebase_activeNextFaceInteraction_mem_currentFaceInteraction
      graphData minimal caps coloring web corridor hunique offset hnext hnextNext
        targetDart.1 targetDart.2 hsupport)

/-- The finite rolling coordinate inclusion is the following rooted state's
facial current-coordinate field. -/
theorem sourceLocalLayerSerialFaceRollingFactorAt_nextCurrentCoordinate_eq
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).crossingEdge step) ≠ 0) :
    (sourceLocalLayerSerialFaceRollingFactorAt graphData minimal caps coloring
      web corridor hunique offset hnext hnextNext).nextCurrentCoordinate =
      (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
        caps coloring web corridor hunique
          (sourceLocalLayerNextOffset offset hnext) hnextNext color hcrossing
        ).faceCurrentCoordinate := by
  rfl

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingSuccessor

end Mettapedia.GraphTheory.FourColor
