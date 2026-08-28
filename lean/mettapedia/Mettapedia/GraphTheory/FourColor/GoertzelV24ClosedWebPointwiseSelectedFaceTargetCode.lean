import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceUniformRecurrence
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedCellPastOverlap
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorForgetExterior
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorSupportedPortProjection

/-!
# Exact selected facial contraction to the next rolling carrier

The exact selected facial rebase lives on at most forty-eight dart
coordinates, while the next rolling state uses at most twenty-four.  This
file constructs the partial coordinate map from the next carrier to the
interaction carrier and proves that every unmapped next coordinate is
inactive.  Consequently the graph-free partial contraction is exactly the
literal successor exterior code.

The proof is occurrence-sensitive.  It first places the edge below a live
target dart in the selected tracked target carrier, applies the strengthened
historical-overlap theorem there, and then returns to the appropriate dart
occurrence in the selected interaction carrier.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedFaceTargetCode

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebPointwiseSelectedCellPastOverlap
open GoertzelV24ClosedWebPointwiseSelectedFaceUniformRecurrence
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FramedTrail
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorForget
open GoertzelV24InterfaceDeletionComponentFactorForgetExterior
open GoertzelV24InterfaceExteriorSupportedPortProjection
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceRegionalDartCarrier
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFaceTargetCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance pointwiseSelectedFaceTargetCodeOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

private theorem carrierCoordinate_symm_apply_apply_val
    {A : Type*} [Fintype A] [DecidableEq A]
    (carrier : Finset A) (point : {a // a ∈ carrier}) :
    ((carrierCoordinate carrier).symm (carrierCoordinate carrier point)).1 =
      point.1 :=
  congrArg Subtype.val ((carrierCoordinate carrier).symm_apply_apply point)

/-- The edge below a selected target facial dart belongs to the selected
tracked target carrier at the same cut. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt_edgeOf_mem_tracked
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (dart : formation.annular.RS.D)
    (hdart : dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset) :
    formation.annular.RS.edgeOf dart ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset := by
  rw [pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt,
    Finset.mem_union] at hdart
  rcases hdart with hcell | houtgoing
  · exact Finset.mem_union_left _ <| Finset.mem_union_left _ <|
      (mem_dartsOnEdges_iff formation.annular.RS _ dart).1 hcell
  · apply Finset.mem_union_left _
    apply Finset.mem_union_right _
    have hedge :=
      edgeOf_mem_edgeAdjacencyClosedCarrier_of_mem_closedDartCarrier
        formation.annular.RS
        (indexedCrossingEdgeSet
          (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
            hinterior offset))
        dart
        (by simpa
          [pointwiseSelectedSourceLocalLayerSerialFaceOutgoingDartCarrierAt]
          using houtgoing)
    simpa [pointwiseSelectedSourceLocalLayerSerialOutgoingEdgeCarrierAt] using
      hedge

/-- Every live selected target dart already occurs in the complete selected
Cell--rebase interaction carrier. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebase_activeFaceTarget_mem_uniform
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (dart : web.annular.RS.D)
    (htarget : dart ∈
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext))
    (hactive : dart ∈
      (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
        web.toFormation corridor hinterior offset hnext).support) :
    dart ∈
      pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        web.toFormation corridor hinterior offset hnext := by
  let targetEdge : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)} :=
    ⟨web.annular.RS.edgeOf dart,
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt_edgeOf_mem_tracked
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext) dart htarget⟩
  rcases (SimpleGraph.mem_support _).1 hactive with ⟨other, hadj⟩
  have hregion : targetEdge.1 ∈
      pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext) :=
    hadj.2.2.1
  rcases
      pointwiseSelectedSourceLocalLayerSerialCellRebase_activeTarget_mem_switch_or_currentCell
        graphData minimal caps coloring web corridor hinterior offset hnext
          targetEdge hregion with hswitch | hcell
  · apply Finset.mem_union_right _
    apply
      pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar
        web.toFormation corridor hinterior offset hnext
    change web.annular.RS.edgeOf dart ∈
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt web.toFormation
        corridor hinterior offset hnext at hswitch
    simpa
      [pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt]
      using hswitch
  · apply Finset.mem_union_left _
    apply Finset.mem_union_left _
    exact (mem_dartsOnEdges_iff web.annular.RS _ dart).2 hcell

/-- Partial coordinate map from the selected next facial carrier into the
selected interaction carrier. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    let target :=
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior (sourceLocalLayerNextOffset offset hnext)
    let interaction :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        formation corridor hinterior offset hnext
    Fin target.card → Option (Fin interaction.card) := by
  classical
  dsimp only
  let target :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
      corridor hinterior (sourceLocalLayerNextOffset offset hnext)
  let interaction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      formation corridor hinterior offset hnext
  intro targetSlot
  let dart := ((carrierCoordinate target).symm targetSlot).1
  if hdart : dart ∈ interaction then
    exact some (carrierCoordinate interaction ⟨dart, hdart⟩)
  else
    exact none

/-- A mapped target coordinate and interaction coordinate name the same
ambient dart occurrence. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt_dart_eq
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (targetSlot : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior (sourceLocalLayerNextOffset offset hnext)).card)
    (interactionSlot : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        formation corridor hinterior offset hnext).card)
    (hsource :
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt
        formation corridor hinterior offset hnext targetSlot =
          some interactionSlot) :
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt formation
        corridor hinterior offset hnext interactionSlot =
      (((carrierCoordinate
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
          formation corridor hinterior
            (sourceLocalLayerNextOffset offset hnext))).symm targetSlot).1) := by
  classical
  let target :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
      corridor hinterior (sourceLocalLayerNextOffset offset hnext)
  let interaction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      formation corridor hinterior offset hnext
  simp only
    [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt,
      id_eq] at hsource
  split at hsource <;> rename_i hdart
  · simp only [Option.some.injEq] at hsource
    subst interactionSlot
    change
      ((carrierCoordinate interaction).symm
        (carrierCoordinate interaction
          ⟨((carrierCoordinate target).symm targetSlot).1, hdart⟩)).1 =
        ((carrierCoordinate target).symm targetSlot).1
    exact carrierCoordinate_symm_apply_apply_val interaction
      ⟨((carrierCoordinate target).symm targetSlot).1, hdart⟩
  · cases hsource

/-- An unmapped target coordinate is inactive in the literal successor
facial graph. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt_none_not_mem_support
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (targetSlot : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)).card)
    (hnone :
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt
        web.toFormation corridor hinterior offset hnext targetSlot = none) :
    (((carrierCoordinate
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext))).symm targetSlot).1) ∉
      (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
        web.toFormation corridor hinterior offset hnext).support := by
  classical
  let target :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
      web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)
  let targetDart : {dart // dart ∈ target} :=
    (carrierCoordinate target).symm targetSlot
  have hnotInteraction : targetDart.1 ∉
      pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        web.toFormation corridor hinterior offset hnext := by
    simp only
      [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt,
        id_eq] at hnone
    split at hnone <;> rename_i hdart
    · cases hnone
    · exact hdart
  intro hsupport
  exact hnotInteraction
    (pointwiseSelectedSourceLocalLayerSerialCellRebase_activeFaceTarget_mem_uniform
      graphData minimal caps coloring web corridor hinterior offset hnext
        targetDart.1 targetDart.2 hsupport)

/-- Executable selected successor code after contraction to the actual next
rolling carrier. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetRawCodeAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    BoundedInterfaceExteriorCode (Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior (sourceLocalLayerNextOffset offset hnext)).card) :=
  partialContractedInterfaceExteriorCode
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
      formation corridor hinterior offset hnext).connectivity
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt
      formation corridor hinterior offset hnext)

/-- The selected target contraction is exactly the literal successor exterior
code on the actual next rolling carrier. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetRawCodeAt_exact
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    let target :=
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)
    let targetDart := fun slot : Fin target.card =>
      ((carrierCoordinate target).symm slot).1
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetRawCodeAt
        web.toFormation corridor hinterior offset hnext =
      exactInterfaceExteriorCode
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
          web.toFormation corridor hinterior offset hnext) targetDart := by
  dsimp only
  let graph :=
    pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
      web.toFormation corridor hinterior offset hnext
  let largerDart :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
      web.toFormation corridor hinterior offset hnext
  let target :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
      web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)
  let targetDart := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let retain :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt
      web.toFormation corridor hinterior offset hnext
  have hcode :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_exact
      web.toFormation corridor hinterior offset hnext
  change partialContractedInterfaceExteriorCode
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
        web.toFormation corridor hinterior offset hnext).connectivity retain =
      exactInterfaceExteriorCode graph targetDart
  rw [hcode]
  have hinjective : Function.Injective targetDart := by
    intro left right heq
    apply (carrierCoordinate target).symm.injective
    exact Subtype.ext heq
  have hsome : ∀ retained slot, retain retained = some slot →
      largerDart slot = targetDart retained := by
    intro retained slot hretain
    exact
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt_dart_eq
        web.toFormation corridor hinterior offset hnext retained slot hretain
  have hnone : ∀ retained, retain retained = none →
      targetDart retained ∉ graph.support := by
    intro retained hretain
    exact
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt_none_not_mem_support
        graphData minimal caps coloring web corridor hinterior offset hnext
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

end GoertzelV24ClosedWebPointwiseSelectedFaceTargetCode

end Mettapedia.GraphTheory.FourColor
