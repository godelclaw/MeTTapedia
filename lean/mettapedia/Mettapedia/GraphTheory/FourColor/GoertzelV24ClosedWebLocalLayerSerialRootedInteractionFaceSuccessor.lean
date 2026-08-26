import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseExact
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCap
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactorMaskUpdate

/-!
# Finite facial successor on the complete interaction carrier

The rooted facial pre-rebase update is exact on the complete forty-eight-dart
interaction carrier.  The remaining boundary rebase is local finite data: a
switch-deletion mask, the successor collar adjacency, and literal successor
activity.  This file packages those rows as a source-independent factor and
proves that its graph-free update is exactly the cap-six facial code of the
literal successor graph.

Target contraction to the next rolling carrier is deliberately separate.  In
particular, no contraction can conceal an inexact uniform rebase.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceSuccessor

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCap
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseExact
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24CorridorProfile
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFactorMaskUpdate
open GoertzelV24InterfaceExteriorLabelCapFactorUpdate
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorTotal
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance rootedInteractionFaceSuccessorOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Finite facial data for the boundary-rebase half of one literal Cell
transition.  The dependent carrier retains its actual cardinality below the
uniform bound; arbitrary inhabitants need not be source-realizable. -/
structure SourceLocalLayerSerialFaceRebaseFactor where
  interactionCount : Fin 49
  switchMask : Fin interactionCount.val → Bool
  localAdjacency :
    Fin interactionCount.val → Fin interactionCount.val → Bool
  localPresent : Fin interactionCount.val → Bool

noncomputable instance :
    DecidableEq SourceLocalLayerSerialFaceRebaseFactor :=
  Classical.decEq _

private abbrev sourceLocalLayerSerialFaceRebaseFactorCode :=
  Σ interactionCount : Fin 49,
    (Fin interactionCount.val → Bool) ×
      (Fin interactionCount.val → Fin interactionCount.val → Bool) ×
      (Fin interactionCount.val → Bool)

private def sourceLocalLayerSerialFaceRebaseFactorEquiv :
    SourceLocalLayerSerialFaceRebaseFactor ≃
      sourceLocalLayerSerialFaceRebaseFactorCode where
  toFun factor := ⟨factor.interactionCount, factor.switchMask,
    factor.localAdjacency, factor.localPresent⟩
  invFun factor := {
    interactionCount := factor.1
    switchMask := factor.2.1
    localAdjacency := factor.2.2.1
    localPresent := factor.2.2.2 }
  left_inv factor := by cases factor; rfl
  right_inv factor := by
    rcases factor with ⟨count, mask, adjacency, present⟩
    rfl

set_option synthInstance.maxSize 256 in
deriving noncomputable instance Fintype for
  sourceLocalLayerSerialFaceRebaseFactorCode

noncomputable instance : Fintype SourceLocalLayerSerialFaceRebaseFactor :=
  Fintype.ofEquiv _ sourceLocalLayerSerialFaceRebaseFactorEquiv.symm

/-- Mask the retired switch darts and adjoin the finite successor collar rows
on the complete interaction carrier. -/
def SourceLocalLayerSerialFaceRebaseFactor.uniformSuccessorCode
    (factor : SourceLocalLayerSerialFaceRebaseFactor)
    (preRebase : SourceLocalLayerSerialFaceInteractionPrefixState)
    (hcount : preRebase.vertexCount = factor.interactionCount) :
    BoundedInterfaceExteriorLabelCapCode
      (Fin factor.interactionCount.val)
      (Fin factor.interactionCount.val × Bool) 6 :=
  addInterfaceAdjacencyAndPresence
    (maskInterfaceExteriorLabelCapCode
      (hcount ▸ preRebase.code ()) Prod.fst factor.switchMask)
    factor.localAdjacency factor.localPresent

/-- Literal finite facial rebase factor on the complete interaction carrier. -/
noncomputable def sourceLocalLayerSerialFaceRebaseFactorAt
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
    SourceLocalLayerSerialFaceRebaseFactor := by
  let interaction := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let dartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  let localGraph := sourceLocalLayerBoundaryRebaseLocalFaceGraphAt corridor
    hunique offset hnext
  let nextRegion := sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext)
  have hinteraction : interaction.card ≤ 48 :=
    sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt_card_le_fortyEight
      graphData minimal caps coloring web corridor hunique offset hnext
  exact {
    interactionCount := ⟨interaction.card, Nat.lt_succ_of_le hinteraction⟩
    switchMask := sourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt
      corridor hunique offset hnext
    localAdjacency := fun left right ↦ by
      classical
      exact decide (localGraph.Adj (dartAt left) (dartAt right))
    localPresent := fun slot ↦ by
      classical
      exact decide (web.annular.RS.edgeOf (dartAt slot) ∈ nextRegion) }

@[simp]
theorem sourceLocalLayerSerialFaceRebaseFactorAt_interactionCount
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
    (sourceLocalLayerSerialFaceRebaseFactorAt graphData minimal caps coloring web
      corridor hunique offset hnext).interactionCount.val =
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        offset hnext).card := by
  rfl

/-- Applying the literal finite factor to the canonical pre-rebase code gives
the exact cap-six code of the literal successor graph. -/
theorem sourceLocalLayerSerialFaceRebaseUniformSuccessorAt_eq
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
    let preRebase := sourceLocalLayerSerialFaceInteractionPreRebaseStateAt
      graphData minimal caps coloring web corridor hunique offset hnext
    let factor := sourceLocalLayerSerialFaceRebaseFactorAt graphData minimal caps
      coloring web corridor hunique offset hnext
    factor.uniformSuccessorCode preRebase (by rfl) =
      sourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
        corridor hunique offset hnext := by
  classical
  dsimp only
  let interaction := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let dartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  let removed := sourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt corridor
    hunique offset hnext
  let preRegion := sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
    offset
  let nextRegion := sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext)
  let preGraph := faceRegionalDartGraph web.annular.RS preRegion
  let coreGraph := sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique
    offset hnext
  let localGraph := sourceLocalLayerBoundaryRebaseLocalFaceGraphAt corridor
    hunique offset hnext
  let successorGraph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
    corridor hunique offset hnext
  let adjacency := fun left right : Fin interaction.card ↦
    decide (localGraph.Adj (dartAt left) (dartAt right))
  let localPresent := fun slot : Fin interaction.card ↦
    decide (web.annular.RS.edgeOf (dartAt slot) ∈ nextRegion)
  have hinjective : Function.Injective dartAt :=
    sourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective corridor hunique
      offset hnext
  have hlocalSupport : localGraph.support ⊆ Set.range dartAt := by
    intro dart hdart
    have hcarrier : dart ∈ interaction :=
      (sourceLocalLayerSerialCell_faceRebase_support_subset_uniformInterface
        corridor hunique offset hnext).2 hdart
    refine ⟨carrierCoordinate interaction ⟨dart, hcarrier⟩, ?_⟩
    simp [dartAt, sourceLocalLayerSerialCellRebaseUniformFaceDartAt, interaction]
  have hmasked := maskInterfaceExteriorLabelCapCode_exact_code_eq preGraph
    dartAt hinjective removed
    (fun dart ↦ web.annular.RS.edgeOf dart ∈ preRegion)
    Prod.fst (faceInterfaceIncidenceVertex web.annular.RS dartAt)
    web.annular.RS.edgeOf 6
  have hsurvival : (fun dart ↦
      web.annular.RS.edgeOf dart ∈ preRegion ∧
        survivesMask dartAt removed dart) =
      (fun dart ↦ web.annular.RS.edgeOf dart ∈
        sourceLocalLayerBoundaryRebaseFaceCoreRegionAt corridor hunique offset
          hnext) := by
    funext dart
    apply propext
    rw [survivesMask_iff_not_removedByInterfaceMask]
    rw [removedBy_uniformFaceSwitchMask_iff corridor hunique offset hnext dart]
    simp [sourceLocalLayerBoundaryRebaseFaceCoreRegionAt, preRegion]
  have hadded := addInterfaceAdjacencyAndPresence_exact_code_eq
    coreGraph localGraph dartAt hlocalSupport
    (fun dart ↦ web.annular.RS.edgeOf dart ∈
      sourceLocalLayerBoundaryRebaseFaceCoreRegionAt corridor hunique offset
        hnext)
    (fun dart ↦ web.annular.RS.edgeOf dart ∈ nextRegion)
    Prod.fst (faceInterfaceIncidenceVertex web.annular.RS dartAt)
    web.annular.RS.edgeOf adjacency (by intro left right; simp [adjacency]) 6
  change addInterfaceAdjacencyAndPresence
      (maskInterfaceExteriorLabelCapCode
        (exactInterfaceExteriorLabelCapCode preGraph dartAt
          (fun dart ↦ web.annular.RS.edgeOf dart ∈ preRegion)
          Prod.fst (faceInterfaceIncidenceVertex web.annular.RS dartAt)
          web.annular.RS.edgeOf 6)
        Prod.fst removed)
      adjacency localPresent =
    exactInterfaceExteriorLabelCapCode successorGraph dartAt
      (fun dart ↦ web.annular.RS.edgeOf dart ∈ nextRegion)
      Prod.fst (faceInterfaceIncidenceVertex web.annular.RS dartAt)
      web.annular.RS.edgeOf 6
  rw [hmasked]
  unfold exactRestrictedInterfaceExteriorLabelCapCode
  rw [restrictedPreRebaseFaceGraph_uniformSwitchMask_eq_core corridor hunique
    offset hnext]
  simp only [hsurvival]
  have hpresent : (fun dart ↦
      web.annular.RS.edgeOf dart ∈
          sourceLocalLayerBoundaryRebaseFaceCoreRegionAt corridor hunique offset
            hnext ∨
        web.annular.RS.edgeOf dart ∈ nextRegion) =
      (fun dart ↦ web.annular.RS.edgeOf dart ∈ nextRegion) := by
    funext dart
    apply propext
    rw [sourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff corridor
      hunique offset hnext]
    simp only [Finset.mem_sdiff]
    tauto
  have hadded' :
      addInterfaceAdjacencyAndPresence
          (exactInterfaceExteriorLabelCapCode coreGraph dartAt
            (fun dart ↦ web.annular.RS.edgeOf dart ∈
              sourceLocalLayerBoundaryRebaseFaceCoreRegionAt corridor hunique
                offset hnext)
            Prod.fst (faceInterfaceIncidenceVertex web.annular.RS dartAt)
            web.annular.RS.edgeOf 6)
          adjacency localPresent =
        exactInterfaceExteriorLabelCapCode (coreGraph ⊔ localGraph) dartAt
          (fun dart ↦ web.annular.RS.edgeOf dart ∈ nextRegion)
          Prod.fst (faceInterfaceIncidenceVertex web.annular.RS dartAt)
          web.annular.RS.edgeOf 6 := by
    calc
      _ = exactInterfaceExteriorLabelCapCode (coreGraph ⊔ localGraph) dartAt
          (fun dart ↦
            web.annular.RS.edgeOf dart ∈
                sourceLocalLayerBoundaryRebaseFaceCoreRegionAt corridor hunique
                  offset hnext ∨
              web.annular.RS.edgeOf dart ∈ nextRegion)
          Prod.fst (faceInterfaceIncidenceVertex web.annular.RS dartAt)
          web.annular.RS.edgeOf 6 := hadded
      _ = exactInterfaceExteriorLabelCapCode (coreGraph ⊔ localGraph) dartAt
          (fun dart ↦ web.annular.RS.edgeOf dart ∈ nextRegion)
          Prod.fst (faceInterfaceIncidenceVertex web.annular.RS dartAt)
          web.annular.RS.edgeOf 6 := by
        congr 1
  rw [hadded']
  exact congrArg
    (fun graph ↦ exactInterfaceExteriorLabelCapCode graph dartAt
      (fun dart ↦ web.annular.RS.edgeOf dart ∈ nextRegion)
      Prod.fst (faceInterfaceIncidenceVertex web.annular.RS dartAt)
      web.annular.RS.edgeOf 6)
    (sourceLocalLayerBoundaryRebaseCore_sup_local_eq_successor corridor hunique
      offset hnext)

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceSuccessor

end Mettapedia.GraphTheory.FourColor
