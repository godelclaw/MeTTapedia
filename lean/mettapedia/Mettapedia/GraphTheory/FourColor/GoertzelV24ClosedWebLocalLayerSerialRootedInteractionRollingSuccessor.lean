import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingLocality
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellColorSplice

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
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
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
open GoertzelV24WindingClassification
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

/-- Locate an ambient edge in the four-role boundary-rebase ABI.  The source
extraction may choose any role when literal edge names coincide; every such
role carries the same ambient colour. -/
noncomputable def boundaryRebaseRoleForEdge?
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) (edge : G.edgeSet) :
    Option SourceLocalLayerBoundaryRebaseRole :=
  if hrole : ∃ role,
      sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role =
        edge then
    some (Classical.choose hrole)
  else none

theorem boundaryRebaseRoleForEdge?_eq_some_edge_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) (edge : G.edgeSet)
    (role : SourceLocalLayerBoundaryRebaseRole)
    (hrole : boundaryRebaseRoleForEdge? corridor hunique offset hnext edge =
      some role) :
    sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role =
      edge := by
  simp only [boundaryRebaseRoleForEdge?] at hrole
  split at hrole <;> rename_i hexists
  · injection hrole with hchosen
    rw [← hchosen]
    exact Classical.choose_spec hexists
  · cases hrole

theorem boundaryRebaseRoleForEdge?_eq_none_not_mem_switch
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) (edge : G.edgeSet)
    (hrole : boundaryRebaseRoleForEdge? corridor hunique offset hnext edge =
      none) :
    edge ∉ sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset
      hnext := by
  rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
  intro hexists
  simp only [boundaryRebaseRoleForEdge?] at hrole
  split at hrole <;> rename_i hfound
  · cases hrole
  · exact hfound hexists

/-- The finite rebase factor together with the partial coordinate map onto the
following interaction carrier and the inclusion of its rolling carrier. -/
structure SourceLocalLayerSerialTrackedRollingFactor where
  rebase : SourceLocalLayerSerialTrackedRebaseFactor
  nextInteractionCount : Fin 50
  nextInteractionSource :
    Fin nextInteractionCount.val → Option (Fin rebase.interactionCount.val)
  nextInteractionActive : Fin nextInteractionCount.val → Bool
  nextColorActive : Fin 49 → Bool
  nextColorRole : Fin 49 → Option SourceLocalLayerBoundaryRebaseRole
  nextColorSource : Fin 49 → Option (Fin 49)
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
      (Fin nextInteractionCount.val → Bool) ×
      (Fin 49 → Bool) ×
      (Fin 49 → Option SourceLocalLayerBoundaryRebaseRole) ×
      (Fin 49 → Option (Fin 49)) ×
        (Fin rebase.targetCount.val → Fin nextInteractionCount.val)

private def sourceLocalLayerSerialTrackedRollingFactorEquiv :
    SourceLocalLayerSerialTrackedRollingFactor ≃
      sourceLocalLayerSerialTrackedRollingFactorCode where
  toFun factor := ⟨factor.rebase, factor.nextInteractionCount,
    factor.nextInteractionSource, factor.nextInteractionActive,
    factor.nextColorActive, factor.nextColorRole, factor.nextColorSource,
    factor.nextCurrentCoordinate⟩
  invFun factor := {
    rebase := factor.1
    nextInteractionCount := factor.2.1
    nextInteractionSource := factor.2.2.1
    nextInteractionActive := factor.2.2.2.1
    nextColorActive := factor.2.2.2.2.1
    nextColorRole := factor.2.2.2.2.2.1
    nextColorSource := factor.2.2.2.2.2.2.1
    nextCurrentCoordinate := factor.2.2.2.2.2.2.2 }
  left_inv factor := by cases factor; rfl
  right_inv factor := by
    rcases factor with
      ⟨rebase, nextCount, source, active, colorActive, colorRole,
        colorSource, coordinate⟩
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

/-- Right-biased union of two colour receipts on the same interaction ABI.
The Cell receipt overrides the accumulated-prefix receipt exactly where the
Cell is present. -/
def sourceLocalLayerSerialTrackedInteractionColorCodeSplice
    (prefixCode cellCode : SourceLocalLayerSerialTrackedInteractionColorCode) :
    SourceLocalLayerSerialTrackedInteractionColorCode := fun slot =>
  match cellCode slot with
  | some color => some color
  | none => prefixCode slot

/-- Encoding the accumulated prefix and the literal Cell separately, then
taking their right-biased union, is exactly the regional colour code of the
literal pre-rebase splice. -/
theorem sourceLocalLayerSerialTrackedInteractionColorCodeSpliceAt_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (carrier : Finset G.edgeSet) (hcard : carrier.card ≤ 49)
    (prefixColor cellColor : G.edgeSet → Color) :
    sourceLocalLayerSerialTrackedInteractionColorCodeSplice
        (sourceLocalLayerSerialTrackedInteractionColorCodeAt carrier hcard
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          prefixColor)
        (sourceLocalLayerSerialTrackedInteractionColorCodeAt carrier hcard
          (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor) =
      sourceLocalLayerSerialTrackedInteractionColorCodeAt carrier hcard
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          prefixColor cellColor) := by
  classical
  funext stable
  by_cases hslot : stable.val < carrier.card
  · let live : Fin carrier.card := ⟨stable.val, hslot⟩
    let edge := ((carrierCoordinate carrier).symm live).1
    have hstable : Fin.castLE hcard live = stable := by
      apply Fin.ext
      rfl
    rw [← hstable]
    simp only [sourceLocalLayerSerialTrackedInteractionColorCodeAt_live]
    by_cases hcell : edge ∈
        sourceLocalLayerCellRegionAt corridor hunique offset
    · have hpre : edge ∈
          sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset := by
        rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor
          hunique offset]
        exact Finset.mem_union_right _ hcell
      simp [sourceLocalLayerSerialTrackedInteractionColorCodeSplice, edge,
        hcell, hpre, sourceLocalLayerSerialCellSplicedColorAt]
    · have hregion : edge ∈
          sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset ↔
        edge ∈ sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          offset := by
        rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor
          hunique offset]
        simp [hcell]
      simp [sourceLocalLayerSerialTrackedInteractionColorCodeSplice, edge,
        hcell, hregion, sourceLocalLayerSerialCellSplicedColorAt]
  · simp [sourceLocalLayerSerialTrackedInteractionColorCodeSplice,
      sourceLocalLayerSerialTrackedInteractionColorCodeAt, hslot]

/-- Roll the exact regional colour table onto the following interaction ABI.
Inactive following coordinates are erased even when the ambient edge is still
named by the current interaction carrier. -/
def SourceLocalLayerSerialTrackedRollingFactor.nextInteractionColorCode
    (factor : SourceLocalLayerSerialTrackedRollingFactor)
    (preRebaseColor : SourceLocalLayerSerialTrackedInteractionColorCode)
    (roleColor : SourceLocalLayerBoundaryRebaseRole → StrandColor) :
    SourceLocalLayerSerialTrackedInteractionColorCode :=
  fun (stableTarget : Fin 49) =>
  if factor.nextColorActive stableTarget then
      match factor.nextColorRole stableTarget with
      | some role => some (StrandColor.toColor (roleColor role))
      | none =>
          match factor.nextColorSource stableTarget with
          | some source =>
              preRebaseColor source
          | none => none
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
  have hcurrentInteraction : currentInteraction.card ≤ 49 :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
      graphData minimal caps coloring web corridor hunique offset hnext
  exact {
    rebase := rebase
    nextInteractionCount :=
      ⟨nextInteraction.card, Nat.lt_succ_of_le hnextInteraction⟩
    nextInteractionSource :=
      finiteCarrierPartialSource currentInteraction nextInteraction
    nextInteractionActive := fun nextSlot => decide
      (((carrierCoordinate nextInteraction).symm nextSlot).1 ∈
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique next)
    nextColorActive := fun stableTarget =>
      if htarget : stableTarget.val < nextInteraction.card then
        decide (((carrierCoordinate nextInteraction).symm
          ⟨stableTarget.val, htarget⟩).1 ∈
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique next)
      else false
    nextColorRole := fun stableTarget =>
      if htarget : stableTarget.val < nextInteraction.card then
        boundaryRebaseRoleForEdge? corridor hunique offset hnext
          ((carrierCoordinate nextInteraction).symm
            ⟨stableTarget.val, htarget⟩).1
      else none
    nextColorSource := fun stableTarget =>
      if htarget : stableTarget.val < nextInteraction.card then
        (finiteCarrierPartialSource currentInteraction nextInteraction
          ⟨stableTarget.val, htarget⟩).map (Fin.castLE hcurrentInteraction)
      else none
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

@[simp]
theorem sourceLocalLayerSerialTrackedRollingFactorAt_nextInteractionActive
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
    (slot : Fin
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
          hnextNext).card) :
    (sourceLocalLayerSerialTrackedRollingFactorAt graphData minimal caps coloring
      web corridor hunique offset hnext hnextNext color
      ).nextInteractionActive slot = decide
        (((carrierCoordinate
          (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
            caps coloring web corridor hunique
              (sourceLocalLayerNextOffset offset hnext) hnextNext)).symm slot).1 ∈
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext)) := by
  rfl

@[simp]
theorem sourceLocalLayerSerialTrackedRollingFactorAt_nextInteractionSource
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
    (slot : Fin
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
          hnextNext).card) :
    (sourceLocalLayerSerialTrackedRollingFactorAt graphData minimal caps coloring
      web corridor hunique offset hnext hnextNext color
      ).nextInteractionSource slot =
        finiteCarrierPartialSource
          (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
            caps coloring web corridor hunique offset hnext)
          (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
            caps coloring web corridor hunique
              (sourceLocalLayerNextOffset offset hnext) hnextNext) slot := by
  rfl

/-- Pointwise decoder equation for the fixed forty-nine-slot colour ABI. -/
theorem sourceLocalLayerSerialTrackedRollingFactorAt_nextInteractionColorCode_apply
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
    (preRebaseColor : SourceLocalLayerSerialTrackedInteractionColorCode)
    (roleColor : SourceLocalLayerBoundaryRebaseRole → StrandColor)
    (stable : Fin 49) :
    let currentInteraction :=
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext
    let next := sourceLocalLayerNextOffset offset hnext
    let nextInteraction :=
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique next hnextNext
    let currentBound : currentInteraction.card ≤ 49 :=
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
        graphData minimal caps coloring web corridor hunique offset hnext
    (sourceLocalLayerSerialTrackedRollingFactorAt graphData minimal caps coloring
      web corridor hunique offset hnext hnextNext color
      ).nextInteractionColorCode preRebaseColor roleColor stable =
      if htarget : stable.val < nextInteraction.card then
        let target : Fin nextInteraction.card := ⟨stable.val, htarget⟩
        let edge := ((carrierCoordinate nextInteraction).symm target).1
        if edge ∈ sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
            next then
          match boundaryRebaseRoleForEdge? corridor hunique offset hnext edge with
          | some role => some (StrandColor.toColor (roleColor role))
          | none =>
              match finiteCarrierPartialSource currentInteraction nextInteraction
                  target with
              | some source => preRebaseColor (Fin.castLE currentBound source)
              | none => none
        else none
      else none := by
  classical
  dsimp only
  unfold SourceLocalLayerSerialTrackedRollingFactor.nextInteractionColorCode
  simp only [sourceLocalLayerSerialTrackedRollingFactorAt]
  by_cases htarget : stable.val <
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
          hnextNext).card
  · simp only [htarget, dif_pos]
    let target : Fin
        (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData
          caps coloring web corridor hunique
            (sourceLocalLayerNextOffset offset hnext) hnextNext).card :=
      ⟨stable.val, htarget⟩
    let edge := ((carrierCoordinate
      (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique (sourceLocalLayerNextOffset offset hnext)
          hnextNext)).symm target).1
    by_cases hactive : edge ∈
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext)
    · simp [target, edge, hactive]
      cases hroleValue : boundaryRebaseRoleForEdge? corridor hunique offset hnext
          edge with
      | some role => rfl
      | none =>
          cases hsource : finiteCarrierPartialSource
              (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
                graphData caps coloring web corridor hunique offset hnext)
              (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
                graphData caps coloring web corridor hunique
                  (sourceLocalLayerNextOffset offset hnext) hnextNext)
              target <;> rfl
    · simp [hactive, target, edge]
  · simp [htarget]

/-- The finite colour recurrence on the forty-nine-slot rolling ABI is exact.
Newly exposed switch coordinates read their colour from the four-role literal
rebase receipt; every other active coordinate is transported from the old
interaction receipt. -/
theorem sourceLocalLayerSerialTrackedRollingNextInteractionColorCodeAt_eq
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
    (hrole : ∀ role, color
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0) :
    let currentInteraction :=
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique offset hnext
    let next := sourceLocalLayerNextOffset offset hnext
    let nextInteraction :=
      sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
        coloring web corridor hunique next hnextNext
    let factor := sourceLocalLayerSerialTrackedRollingFactorAt graphData minimal
      caps coloring web corridor hunique offset hnext hnextNext color
    factor.nextInteractionColorCode
        (sourceLocalLayerSerialTrackedInteractionColorCodeAt currentInteraction
          (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
            graphData minimal caps coloring web corridor hunique offset hnext)
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
          color)
        (successorTrackedStateForColorAt corridor hunique offset hnext color
          hrole).roleColor =
      sourceLocalLayerSerialTrackedInteractionColorCodeAt nextInteraction
        (sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
          graphData minimal caps coloring web corridor hunique next hnextNext)
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique next) color := by
  classical
  dsimp only
  let currentInteraction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique offset hnext
  let next := sourceLocalLayerNextOffset offset hnext
  let nextInteraction :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt graphData caps
      coloring web corridor hunique next hnextNext
  let currentBound : currentInteraction.card ≤ 49 :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
      graphData minimal caps coloring web corridor hunique offset hnext
  let nextBound : nextInteraction.card ≤ 49 :=
    sourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt_card_le_fortyNine
      graphData minimal caps coloring web corridor hunique next hnextNext
  funext stable
  rw [sourceLocalLayerSerialTrackedRollingFactorAt_nextInteractionColorCode_apply]
  by_cases hslot : stable.val < nextInteraction.card
  · let target : Fin nextInteraction.card := ⟨stable.val, hslot⟩
    let edge := ((carrierCoordinate nextInteraction).symm target).1
    rw [dif_pos hslot]
    dsimp only
    have hstable : Fin.castLE nextBound target = stable := by
      apply Fin.ext
      rfl
    have htargetCode :
        sourceLocalLayerSerialTrackedInteractionColorCodeAt nextInteraction
            nextBound
            (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique next)
            color stable =
          if edge ∈
              sourceLocalLayerSerialTerminalInputRegionAt corridor hunique next
          then some (color edge) else none := by
      rw [← hstable,
        sourceLocalLayerSerialTrackedInteractionColorCodeAt_live]
    rw [htargetCode]
    by_cases hactive : edge ∈
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique next
    · rw [if_pos hactive]
      cases hroleSlot : boundaryRebaseRoleForEdge? corridor hunique offset hnext
          edge with
      | some role =>
          have hedge := boundaryRebaseRoleForEdge?_eq_some_edge_eq corridor
            hunique offset hnext edge role hroleSlot
          simp only [hactive, if_true]
          simp [successorTrackedStateForColorAt, hedge]
      | none =>
          have hnotSwitch :=
            boundaryRebaseRoleForEdge?_eq_none_not_mem_switch corridor hunique
              offset hnext edge hroleSlot
          have hpre : edge ∈
              sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
                offset :=
            (sourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
              corridor hunique offset hnext edge hnotSwitch).2 hactive
          let targetEdge : {edge // edge ∈ nextInteraction} :=
            (carrierCoordinate nextInteraction).symm target
          have hcurrent : edge ∈ currentInteraction := by
            exact
              sourceLocalLayerSerialCellRebase_activeNextInteraction_mem_currentInteraction
                graphData minimal caps coloring web corridor hunique offset
                  hnext hnextNext targetEdge hactive
          let currentSlot : Fin currentInteraction.card :=
            carrierCoordinate currentInteraction ⟨edge, hcurrent⟩
          have hsource : finiteCarrierPartialSource currentInteraction
              nextInteraction target = some currentSlot := by
            simp only [finiteCarrierPartialSource]
            rw [dif_pos hcurrent]
          have hpreCode :
              sourceLocalLayerSerialTrackedInteractionColorCodeAt
                  currentInteraction currentBound
                  (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor
                    hunique offset) color
                  (Fin.castLE currentBound currentSlot) = some (color edge) := by
            rw [sourceLocalLayerSerialTrackedInteractionColorCodeAt_live]
            have hcurrentSlotEdge :
                ((carrierCoordinate currentInteraction).symm currentSlot).1 =
                  edge := by
              simp [currentSlot]
            rw [hcurrentSlotEdge, if_pos hpre]
          simp only [hactive, if_true]
          rw [hsource]
          exact hpreCode
    · rw [if_neg hactive]
      rw [if_neg hactive]
  · rw [dif_neg hslot]
    change none = if _h : stable.val < nextInteraction.card then _ else none
    rw [dif_neg hslot]

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
