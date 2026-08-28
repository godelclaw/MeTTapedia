import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedCellPastOverlap
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedRebaseFactor
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorSupportedPortProjection

/-!
# Exact selected tracked target contraction

The finite rebase factor computes its successor on the complete forty-nine-
slot interaction carrier.  This file contracts that code to the next
twenty-one-slot rolling carrier.

The only non-generic input is the selected historical-overlap theorem: a
target coordinate not represented in the interaction carrier is isolated in
the literal successor graph.  The generic partial-contraction lemmas then make
all three exterior-code rows exact.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedTrackedTargetCode

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebPointwiseSelectedCellPastOverlap
open GoertzelV24ClosedWebPointwiseSelectedTrackedRebaseFactor
open GoertzelV24ClosedWebPointwiseSelectedTrackedUniformRecurrence
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

local instance pointwiseSelectedTrackedTargetCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance pointwiseSelectedTrackedTargetCodeOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- An unmapped target coordinate is isolated in every literal selected
successor tracked graph. -/
theorem
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt_none_not_mem_support
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair)
    (targetSlot : Fin
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)).card)
    (hnone :
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt
        web corridor hinterior offset hnext targetSlot = none) :
    (((carrierCoordinate
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext))).symm targetSlot).1) ∉
      (pointwiseSelectedSuccessorTrackedGraphForColorAt web.toFormation
        corridor hinterior offset hnext color pair).support := by
  classical
  let target :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)
  let targetEdge : {edge // edge ∈ target} :=
    (carrierCoordinate target).symm targetSlot
  let interaction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web.toFormation corridor hinterior offset hnext
  have hnotInteraction : targetEdge.1 ∉ interaction := by
    simp only
      [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt,
        id_eq] at hnone
    split at hnone <;> rename_i hedge
    · cases hnone
    · exact hedge
  intro hsupport
  rcases (SimpleGraph.mem_support _).1 hsupport with ⟨other, hadj⟩
  have hactive : targetEdge.1 ∈
      pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext) := by
    exact hadj.2.1
  have hcovered :=
    pointwiseSelectedSourceLocalLayerSerialCellRebase_activeTarget_mem_switch_or_currentCell
      graphData minimal caps coloring web corridor hinterior offset hnext
        targetEdge hactive
  apply hnotInteraction
  rcases hcovered with hswitch | hcurrent
  · exact
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitch_subset_uniformTrackedCarrier
        web corridor hinterior offset hnext hswitch
  · apply
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_subset_interaction
        web.toFormation corridor hinterior offset hnext
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hcurrent)

/-- The graph-free partial contraction is the canonical exterior code on the
literal next selected rolling carrier. -/
theorem
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetRawCodeAt_exact
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
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair) :
    let target :=
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)
    let targetVertex := fun slot : Fin target.card ↦
      ((carrierCoordinate target).symm slot).1
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetRawCodeAt
        web corridor hinterior offset hnext color pair =
      exactInterfaceExteriorCode
        (pointwiseSelectedSuccessorTrackedGraphForColorAt web.toFormation
          corridor hinterior offset hnext color pair) targetVertex := by
  dsimp only
  let graph :=
    pointwiseSelectedSuccessorTrackedGraphForColorAt web.toFormation corridor
      hinterior offset hnext color pair
  let largerVertex :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt web
      corridor hinterior offset hnext
  let target :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)
  let targetVertex := fun slot : Fin target.card ↦
    ((carrierCoordinate target).symm slot).1
  let retain :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt
      web corridor hinterior offset hnext
  have hcode :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedSuccessorCodeAt_exact
      web corridor hinterior offset hnext color pair
  change partialContractedInterfaceExteriorCode
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedSuccessorRawCodeAt
        web corridor hinterior offset hnext color pair) retain =
      exactInterfaceExteriorCode graph targetVertex
  rw [hcode]
  have hinjective : Function.Injective targetVertex := by
    intro left right heq
    apply (carrierCoordinate target).symm.injective
    exact Subtype.ext heq
  have hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = targetVertex retained := by
    intro retained slot hretain
    exact
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt_edge_eq
        web corridor hinterior offset hnext retained slot hretain
  have hnone : ∀ retained, retain retained = none →
      targetVertex retained ∉ graph.support := by
    intro retained hretain
    exact
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetSourceAt_none_not_mem_support
        graphData minimal caps coloring web corridor hinterior offset hnext color
          pair retained hretain
  apply boundedInterfaceExteriorCode_ext_iff
  · intro left right
    change partialReindexedVertexEq left right = true ↔
      (exactInterfaceExteriorCode graph targetVertex).vertexEq left right = true
    rw [partialReindexedVertexEq_eq_true_iff targetVertex hinjective]
    simp [exactInterfaceExteriorCode]
  · intro left right
    change partialReindexedDirectAdj
        (exactInterfaceExteriorCode graph largerVertex) retain left right = true ↔
      (exactInterfaceExteriorCode graph targetVertex).directAdj left right = true
    rw [partialReindexedDirectAdj_exact_iff graph largerVertex targetVertex
      retain hsome hnone left right]
    simp [exactInterfaceExteriorCode]
  · intro left right
    change partialReindexedExteriorConnected
        (exactInterfaceExteriorCode graph largerVertex) retain left right = true ↔
      (exactInterfaceExteriorCode graph targetVertex).exteriorConnected left
        right = true
    rw [partialReindexedExteriorConnected_exact_eq_true_iff graph largerVertex
      targetVertex retain hsome hnone left right]
    simp [exactInterfaceExteriorCode]

/-- Consumer-facing exactness of the finite selected rebase factor: applying
its target-state constructor to the exact interaction state produces the
canonical code on the next literal rolling carrier. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedRebaseFactorAt_targetState_code_exact
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
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (hcellNext :
      (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)).card ≤ 6)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair) :
    let preRebase :=
      pointwiseSelectedSourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
        web corridor hinterior offset hnext hcell color
    let factor :=
      pointwiseSelectedSourceLocalLayerSerialTrackedRebaseFactorAt web corridor
        hinterior offset hnext hcell hcellNext color
    let target :=
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)
    let targetVertex := fun slot : Fin target.card ↦
      ((carrierCoordinate target).symm slot).1
    (factor.targetState preRebase (by rfl)).code pair =
      exactInterfaceExteriorCode
        (pointwiseSelectedSuccessorTrackedGraphForColorAt web.toFormation
          corridor hinterior offset hnext color pair) targetVertex := by
  dsimp only
  change
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetRawCodeAt
        web corridor hinterior offset hnext color pair = _
  exact
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedTargetRawCodeAt_exact
      graphData minimal caps coloring web corridor hinterior offset hnext color
        pair

end

end GoertzelV24ClosedWebPointwiseSelectedTrackedTargetCode

end Mettapedia.GraphTheory.FourColor
