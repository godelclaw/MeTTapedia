import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingLocality

/-!
# Exact rolling successor for the rooted interaction code

The current interaction code is updated by the literal Cell and rebase on its
forty-nine-coordinate carrier.  Rolling locality proves that every active
coordinate of the following interaction carrier is already named there.
Consequently the same generic partial contraction used for the
twenty-one-coordinate target also computes the complete following lookahead
root.

This file packages the extra rolling data as a finite factor, defines the
graph-free contraction, and proves exactness on arbitrary literal source
prefixes.  It closes the unbounded-receipt risk: the rooted exterior code rolls
from one fixed bound of forty-nine coordinates to another.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingSuccessor

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedRecurrence
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingLocality
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionTrackedSuccessor
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorForget
open GoertzelV24InterfaceDeletionComponentFactorForgetExterior
open GoertzelV24InterfaceExteriorSupportedPortProjection
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance rootedInteractionRollingSuccessorOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The finite rebase factor together with the partial coordinate map onto the
following interaction carrier and the inclusion of its rolling carrier. -/
structure SourceLocalLayerSerialTrackedRollingFactor where
  rebase : SourceLocalLayerSerialTrackedRebaseFactor
  nextInteractionCount : Fin 50
  nextInteractionSource :
    Fin nextInteractionCount.val → Option (Fin rebase.interactionCount.val)
  nextCurrentCoordinate :
    Fin rebase.targetCount.val → Fin nextInteractionCount.val

noncomputable instance :
    DecidableEq SourceLocalLayerSerialTrackedRollingFactor :=
  Classical.decEq _

private abbrev sourceLocalLayerSerialTrackedRollingFactorCode :=
  Σ rebase : SourceLocalLayerSerialTrackedRebaseFactor,
    Σ nextInteractionCount : Fin 50,
      (Fin nextInteractionCount.val →
        Option (Fin rebase.interactionCount.val)) ×
      (Fin rebase.targetCount.val → Fin nextInteractionCount.val)

private def sourceLocalLayerSerialTrackedRollingFactorEquiv :
    SourceLocalLayerSerialTrackedRollingFactor ≃
      sourceLocalLayerSerialTrackedRollingFactorCode where
  toFun factor := ⟨factor.rebase, factor.nextInteractionCount,
    factor.nextInteractionSource, factor.nextCurrentCoordinate⟩
  invFun factor := {
    rebase := factor.1
    nextInteractionCount := factor.2.1
    nextInteractionSource := factor.2.2.1
    nextCurrentCoordinate := factor.2.2.2 }
  left_inv factor := by cases factor; rfl
  right_inv factor := by
    rcases factor with ⟨rebase, nextCount, source, coordinate⟩
    rfl

set_option synthInstance.maxSize 256 in
deriving noncomputable instance Fintype for
  sourceLocalLayerSerialTrackedRollingFactorCode

noncomputable instance : Fintype SourceLocalLayerSerialTrackedRollingFactor :=
  Fintype.ofEquiv _ sourceLocalLayerSerialTrackedRollingFactorEquiv.symm

/-- Partial coordinate map from a target carrier back into a source carrier.
It is defined entirely from the two finite carriers and is therefore reusable
by every bounded rolling transition. -/
noncomputable def finiteCarrierPartialSource {α : Type*} [Fintype α] [DecidableEq α]
    (source target : Finset α) :
    Fin target.card → Option (Fin source.card) := fun targetSlot =>
  let value := ((carrierCoordinate target).symm targetSlot).1
  if hvalue : value ∈ source then
    some (carrierCoordinate source ⟨value, hvalue⟩)
  else none

/-- A successful finite-carrier source lookup names the same ambient value. -/
theorem finiteCarrierPartialSource_eq_some_value_eq {α : Type*} [Fintype α]
    [DecidableEq α]
    (source target : Finset α)
    (targetSlot : Fin target.card)
    (sourceSlot : Fin source.card)
    (hsource : finiteCarrierPartialSource source target targetSlot =
      some sourceSlot) :
    ((carrierCoordinate source).symm sourceSlot).1 =
      ((carrierCoordinate target).symm targetSlot).1 := by
  classical
  simp only [finiteCarrierPartialSource] at hsource
  split at hsource <;> rename_i hvalue
  · injection hsource with hslot
    rw [← hslot]
    exact congrArg Subtype.val
      ((carrierCoordinate source).symm_apply_apply
        ⟨((carrierCoordinate target).symm targetSlot).1, hvalue⟩)
  · cases hsource

/-- A failed finite-carrier source lookup is exactly non-membership in the
source carrier. -/
theorem finiteCarrierPartialSource_eq_none_not_mem {α : Type*} [Fintype α]
    [DecidableEq α]
    (source target : Finset α)
    (targetSlot : Fin target.card)
    (hsource : finiteCarrierPartialSource source target targetSlot = none) :
    ((carrierCoordinate target).symm targetSlot).1 ∉ source := by
  classical
  simp only [finiteCarrierPartialSource] at hsource
  split at hsource <;> rename_i hvalue
  · cases hsource
  · exact hvalue

/-- Contract the updated current interaction code onto the following
interaction carrier. -/
def SourceLocalLayerSerialTrackedRollingFactor.nextInteractionState
    (factor : SourceLocalLayerSerialTrackedRollingFactor)
    (preRebase : SourceLocalLayerSerialTrackedInteractionPrefixState)
    (hcount : preRebase.vertexCount = factor.rebase.interactionCount) :
    SourceLocalLayerSerialTrackedInteractionPrefixState where
  vertexCount := factor.nextInteractionCount
  code := fun pair => partialContractedInterfaceExteriorCode
    (factor.rebase.uniformSuccessorCode preRebase hcount pair)
    factor.nextInteractionSource

/-- Guarded executable form of the rolling interaction contraction. -/
def SourceLocalLayerSerialTrackedRollingFactor.nextInteractionState?
    (factor : SourceLocalLayerSerialTrackedRollingFactor)
    (preRebase : SourceLocalLayerSerialTrackedInteractionPrefixState) :
    Option SourceLocalLayerSerialTrackedInteractionPrefixState :=
  if hcount : preRebase.vertexCount = factor.rebase.interactionCount then
    some (factor.nextInteractionState preRebase hcount)
  else none

/-- The literal finite rolling factor for two consecutive interior
Cell--rebase positions. -/
noncomputable def sourceLocalLayerSerialTrackedRollingFactorAt
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
    SourceLocalLayerSerialTrackedRollingFactor := by
  classical
  let rebase := sourceLocalLayerSerialTrackedRebaseFactorAt graphData minimal
    caps coloring web corridor hunique offset hnext color
  let next := sourceLocalLayerNextOffset offset hnext
  let currentInteraction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  let target := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique next
  let nextInteraction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique next hnextNext
  have hnextInteraction : nextInteraction.card ≤ 49 :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
      graphData minimal caps coloring web corridor hunique next hnextNext
  exact {
    rebase := rebase
    nextInteractionCount :=
      ⟨nextInteraction.card, Nat.lt_succ_of_le hnextInteraction⟩
    nextInteractionSource :=
      finiteCarrierPartialSource currentInteraction nextInteraction
    nextCurrentCoordinate := fun targetSlot =>
      carrierCoordinate nextInteraction
        ⟨((carrierCoordinate target).symm targetSlot).1,
          Finset.mem_union_left _ ((carrierCoordinate target).symm
            targetSlot).2⟩ }

@[simp]
theorem sourceLocalLayerSerialTrackedRollingFactorAt_nextInteractionCount
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
    (sourceLocalLayerSerialTrackedRollingFactorAt graphData minimal caps coloring
      web corridor hunique offset hnext hnextNext color
      ).nextInteractionCount.val =
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
          hnextNext).card := by
  rfl

/-- A mapped following-interaction coordinate denotes the same ambient edge. -/
theorem sourceLocalLayerSerialTrackedRollingFactorAt_nextInteractionSource_edge_eq
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
    (nextSlot : Fin
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
          hnextNext).card)
    (currentSlot : Fin
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext).card)
    (hsource :
      (sourceLocalLayerSerialTrackedRollingFactorAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext color
        ).nextInteractionSource nextSlot = some currentSlot) :
    sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt graphData caps coloring
        web corridor hunique offset hnext currentSlot =
      (((carrierCoordinate
        (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
          caps coloring web corridor hunique
            (sourceLocalLayerNextOffset offset hnext) hnextNext)
        ).symm nextSlot).1) := by
  let currentInteraction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  let nextInteraction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
        hnextNext
  change finiteCarrierPartialSource currentInteraction nextInteraction nextSlot =
    some currentSlot at hsource
  exact finiteCarrierPartialSource_eq_some_value_eq currentInteraction
    nextInteraction nextSlot currentSlot hsource

/-- An unmapped coordinate is inactive in the literal successor graph. -/
theorem sourceLocalLayerSerialTrackedRollingFactorAt_nextInteractionSource_none_not_mem_support
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
    (pair : TrackedColorPair)
    (nextSlot : Fin
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
          hnextNext).card)
    (hnone :
      (sourceLocalLayerSerialTrackedRollingFactorAt graphData minimal caps
        coloring web corridor hunique offset hnext hnextNext color
        ).nextInteractionSource nextSlot = none) :
    (((carrierCoordinate
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
          hnextNext)).symm nextSlot).1) ∉
      (successorTrackedGraphForColorAt corridor hunique offset hnext color pair
        ).support := by
  classical
  let nextInteraction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
        hnextNext
  let targetEdge : {edge // edge ∈ nextInteraction} :=
    (carrierCoordinate nextInteraction).symm nextSlot
  have hnotCurrent : targetEdge.1 ∉
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext := by
    let currentInteraction :=
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext
    change finiteCarrierPartialSource currentInteraction nextInteraction nextSlot =
      none at hnone
    exact finiteCarrierPartialSource_eq_none_not_mem currentInteraction
      nextInteraction nextSlot hnone
  exact sourceLocalLayerSerialCellRebase_nextInteraction_none_not_mem_support
    graphData minimal caps coloring web corridor hunique offset hnext hnextNext
      color pair targetEdge hnotCurrent

/-- Rowwise exactness of the rolling interaction contraction. -/
theorem sourceLocalLayerSerialTrackedRollingNextInteractionStateAt_code_eq
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
    (pair : TrackedColorPair) :
    let preRebase :=
      sourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt graphData
        minimal caps coloring web corridor hunique offset hnext color
    let factor := sourceLocalLayerSerialTrackedRollingFactorAt graphData minimal
      caps coloring web corridor hunique offset hnext hnextNext color
    let nextInteraction :=
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
          hnextNext
    (factor.nextInteractionState preRebase (by rfl)).code pair =
      exactInterfaceExteriorCode
        (successorTrackedGraphForColorAt corridor hunique offset hnext color pair)
        (fun slot : Fin nextInteraction.card =>
          ((carrierCoordinate nextInteraction).symm slot).1) := by
  dsimp only
  let graph := successorTrackedGraphForColorAt corridor hunique offset hnext
    color pair
  let currentInteraction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  let currentVertex := sourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt
    graphData caps coloring web corridor hunique offset hnext
  let nextInteraction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
        hnextNext
  let nextVertex := fun slot : Fin nextInteraction.card =>
    ((carrierCoordinate nextInteraction).symm slot).1
  let retain := finiteCarrierPartialSource currentInteraction nextInteraction
  change partialContractedInterfaceExteriorCode
      (sourceLocalLayerSerialCellRebaseUniformTrackedSuccessorRawCodeAt graphData
        caps coloring web corridor hunique offset hnext color pair) retain =
      exactInterfaceExteriorCode graph nextVertex
  rw [sourceLocalLayerSerialCellRebaseUniformTrackedSuccessorCodeAt_exact
    graphData caps coloring web corridor hunique offset hnext color pair]
  have hinjective : Function.Injective nextVertex := by
    intro left right heq
    apply (carrierCoordinate nextInteraction).symm.injective
    exact Subtype.ext heq
  have hsome : ∀ retained slot, retain retained = some slot →
      currentVertex slot = nextVertex retained := by
    intro retained slot hretain
    exact finiteCarrierPartialSource_eq_some_value_eq currentInteraction
      nextInteraction retained slot hretain
  have hnone : ∀ retained, retain retained = none →
      nextVertex retained ∉ graph.support := by
    intro retained hretain
    let targetEdge : {edge // edge ∈ nextInteraction} :=
      (carrierCoordinate nextInteraction).symm retained
    have hnotCurrent : targetEdge.1 ∉ currentInteraction := by
      exact finiteCarrierPartialSource_eq_none_not_mem currentInteraction
        nextInteraction retained hretain
    exact sourceLocalLayerSerialCellRebase_nextInteraction_none_not_mem_support
      graphData minimal caps coloring web corridor hunique offset hnext hnextNext
        color pair targetEdge hnotCurrent
  apply boundedInterfaceExteriorCode_ext_iff
  · intro left right
    change partialReindexedVertexEq left right = true ↔
      (exactInterfaceExteriorCode graph nextVertex).vertexEq left right = true
    rw [partialReindexedVertexEq_eq_true_iff nextVertex hinjective]
    simp [exactInterfaceExteriorCode]
  · intro left right
    change partialReindexedDirectAdj
        (exactInterfaceExteriorCode graph currentVertex) retain left right =
          true ↔
      (exactInterfaceExteriorCode graph nextVertex).directAdj left right = true
    rw [partialReindexedDirectAdj_exact_iff graph currentVertex nextVertex retain
      hsome hnone left right]
    simp [exactInterfaceExteriorCode]
  · intro left right
    change partialReindexedExteriorConnected
        (exactInterfaceExteriorCode graph currentVertex) retain left right =
          true ↔
      (exactInterfaceExteriorCode graph nextVertex).exteriorConnected left
        right = true
    rw [partialReindexedExteriorConnected_exact_eq_true_iff graph currentVertex
      nextVertex retain hsome hnone left right]
    simp [exactInterfaceExteriorCode]

/-- The rolling finite contraction is exactly the interaction-exterior field
of the canonical next rooted source state. -/
theorem sourceLocalLayerSerialTrackedRollingNextInteractionStateAt_eq
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
    let preRebase :=
      sourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt graphData
        minimal caps coloring web corridor hunique offset hnext color
    let factor := sourceLocalLayerSerialTrackedRollingFactorAt graphData minimal
      caps coloring web corridor hunique offset hnext hnextNext color
    factor.nextInteractionState preRebase (by rfl) =
      (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
        caps coloring web corridor hunique
          (sourceLocalLayerNextOffset offset hnext) hnextNext color hcrossing
        ).interactionExterior := by
  dsimp only
  rw [BoundedInterfaceExteriorFamilyCode.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  funext pair
  rw [sourceLocalLayerSerialTrackedRollingNextInteractionStateAt_code_eq
    graphData minimal caps coloring web corridor hunique offset hnext hnextNext
      color pair]
  rfl

/-- The finite rolling coordinate inclusion is exactly the following rooted
state's current-coordinate field. -/
theorem sourceLocalLayerSerialTrackedRollingFactorAt_nextCurrentCoordinate_eq
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
    (sourceLocalLayerSerialTrackedRollingFactorAt graphData minimal caps coloring
      web corridor hunique offset hnext hnextNext color
      ).nextCurrentCoordinate =
      (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
        caps coloring web corridor hunique
          (sourceLocalLayerNextOffset offset hnext) hnextNext color hcrossing
        ).currentCoordinate := by
  rfl

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingSuccessor

end Mettapedia.GraphTheory.FourColor
