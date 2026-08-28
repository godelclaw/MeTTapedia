import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedBoundaryRebaseFaceRecurrence
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseState
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactorMaskUpdate

/-!
# Exact selected facial recurrence on the complete interaction carrier

The pointwise-selected current carrier and the following rebase collar form a
complete interface of at most forty-eight darts.  This file gives that carrier
canonical coordinates, deletes exactly the four switch-edge occurrences, adds
the local successor residual, and proves the resulting cap-six code equal to
the literal successor regional face graph.

This is the exact uniform rebase layer.  Contraction to the following
twenty-four-dart rolling carrier is intentionally left to the next module.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedFaceUniformRecurrence

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseState
open GoertzelV24CorridorProfile
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24InterfaceDeletionComponentFactorMaskUpdate
open GoertzelV24InterfaceDeletionComponentFactorTotal
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFactorMaskUpdate
open GoertzelV24InterfaceExteriorLabelCapFactorUpdate
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFaceUniformRecurrenceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Ambient dart represented by one selected uniform facial coordinate. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Fin (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      formation corridor hinterior offset hnext).card →
      formation.annular.RS.D :=
  fun slot =>
    ((carrierCoordinate
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        formation corridor hinterior offset hnext)).symm slot).1

/-- Selected uniform facial coordinates name distinct ambient darts. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Function.Injective
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
        formation corridor hinterior offset hnext) := by
  intro left right heq
  apply (carrierCoordinate
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      formation corridor hinterior offset hnext)).symm.injective
  exact Subtype.ext heq

/-- Every dart over a switch edge is represented by the uniform carrier. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDarts_subset_uniformFaceCarrier
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt formation
        corridor hinterior offset hnext ⊆
      pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        formation corridor hinterior offset hnext := by
  intro dart hdart
  exact Finset.mem_union_right _
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar
      formation corridor hinterior offset hnext hdart)

/-- Boolean mask selecting precisely the dart occurrences over the selected
four-edge switch. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Fin (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      formation corridor hinterior offset hnext).card → Bool :=
  fun slot => decide
    (formation.annular.RS.edgeOf
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
          formation corridor hinterior offset hnext slot) ∈
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation corridor
        hinterior offset hnext)

/-- The coordinate mask removes exactly the ambient switch occurrences. -/
theorem pointwiseSelected_removedBy_uniformFaceSwitchMask_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (dart : formation.annular.RS.D) :
    RemovedByInterfaceMask
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
          formation corridor hinterior offset hnext)
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt
          formation corridor hinterior offset hnext) dart ↔
      formation.annular.RS.edgeOf dart ∈
        pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation
          corridor hinterior offset hnext := by
  let carrier :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      formation corridor hinterior offset hnext
  let dartAt :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt formation
      corridor hinterior offset hnext
  let removed :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt
      formation corridor hinterior offset hnext
  constructor
  · rintro ⟨slot, hremoved, rfl⟩
    simpa [removed,
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt]
      using hremoved
  · intro hdart
    have hchanged : dart ∈
        pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt
          formation corridor hinterior offset hnext := by
      simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt]
        using hdart
    have hcarrier : dart ∈ carrier :=
      pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDarts_subset_uniformFaceCarrier
        formation corridor hinterior offset hnext hchanged
    let slot : Fin carrier.card := carrierCoordinate carrier ⟨dart, hcarrier⟩
    have hdartAt : dartAt slot = dart := by
      simp [dartAt,
        pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt,
        slot, carrier]
    refine ⟨slot, ?_, hdartAt.symm⟩
    change decide
        (formation.annular.RS.edgeOf (dartAt slot) ∈
          pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation
            corridor hinterior offset hnext) = true
    rw [hdartAt]
    exact decide_eq_true hdart

/-- Masking the selected pre-rebase face graph gives the literal common core. -/
theorem pointwiseSelected_restrictedPreRebaseFaceGraph_uniformSwitchMask_eq_core
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    let graph := faceRegionalDartGraph formation.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
        corridor hinterior offset)
    restrictedByMask graph
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
          formation corridor hinterior offset hnext)
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt
          formation corridor hinterior offset hnext) =
      pointwiseSelectedSourceLocalLayerBoundaryRebaseCoreFaceGraphAt formation
        corridor hinterior offset hnext := by
  dsimp only
  let graph := faceRegionalDartGraph formation.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
      corridor hinterior offset)
  let dartAt :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt formation
      corridor hinterior offset hnext
  let removed :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt
      formation corridor hinterior offset hnext
  have hsurvives : survivesMask dartAt removed = fun dart =>
      formation.annular.RS.edgeOf dart ∉
        pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation
          corridor hinterior offset hnext := by
    funext dart
    apply propext
    rw [survivesMask_iff_not_removedByInterfaceMask]
    rw [pointwiseSelected_removedBy_uniformFaceSwitchMask_iff formation corridor
      hinterior offset hnext dart]
  rw [restrictedByMask, hsurvives]
  ext left right
  simp only [supportRestriction_adj,
    pointwiseSelectedSourceLocalLayerBoundaryRebaseCoreFaceGraphAt,
    faceRegionalDartGraph_adj,
    pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCoreRegionAt,
    Finset.mem_sdiff]
  tauto

/-- Exact selected cap-six pre-rebase state on the complete interaction
carrier. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceInteractionPreRebaseStateAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6) :
    SourceLocalLayerSerialFaceInteractionPrefixState := by
  let carrier :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      formation corridor hinterior offset hnext
  let hcarrier : carrier.card ≤ 48 :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt_card_le_fortyEight
      formation corridor hinterior offset hnext hcell
  let dartAt :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt formation
      corridor hinterior offset hnext
  exact {
    vertexCount := ⟨carrier.card, Nat.lt_succ_of_le hcarrier⟩
    code := fun _ => exactFaceInterfaceExteriorLabelCapCode formation.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
        corridor hinterior offset) dartAt 6 }

/-- Executable selected facial rebase on the complete interaction carrier. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    BoundedInterfaceExteriorLabelCapCode
      (Fin (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        formation corridor hinterior offset hnext).card)
      (Fin (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        formation corridor hinterior offset hnext).card × Bool) 6 :=
  let dartAt :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt formation
      corridor hinterior offset hnext
  let removed :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt
      formation corridor hinterior offset hnext
  let preRegion :=
    pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
      corridor hinterior offset
  let nextRegion :=
    pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior (sourceLocalLayerNextOffset offset hnext)
  let localGraph :=
    pointwiseSelectedSourceLocalLayerBoundaryRebaseLocalFaceGraphAt formation
      corridor hinterior offset hnext
  addInterfaceAdjacencyAndPresence
    (maskInterfaceExteriorLabelCapCode
      (exactFaceInterfaceExteriorLabelCapCode formation.annular.RS preRegion
        dartAt 6)
      Prod.fst removed)
    (fun left right => by
      classical
      exact decide (localGraph.Adj (dartAt left) (dartAt right)))
    (fun slot => decide
      (formation.annular.RS.edgeOf (dartAt slot) ∈ nextRegion))

/-- The finite selected facial rebase is exactly the cap-six code of the
literal successor regional graph on every uniform coordinate. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_exact
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    let dartAt :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
        formation corridor hinterior offset hnext
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
        formation corridor hinterior offset hnext =
      exactFaceInterfaceExteriorLabelCapCode formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior (sourceLocalLayerNextOffset offset hnext))
        dartAt 6 := by
  classical
  unfold pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
  dsimp only
  let interaction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      formation corridor hinterior offset hnext
  let dartAt :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt formation
      corridor hinterior offset hnext
  let removed :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt
      formation corridor hinterior offset hnext
  let preRegion :=
    pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
      corridor hinterior offset
  let nextRegion :=
    pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior (sourceLocalLayerNextOffset offset hnext)
  let preGraph := faceRegionalDartGraph formation.annular.RS preRegion
  let coreGraph :=
    pointwiseSelectedSourceLocalLayerBoundaryRebaseCoreFaceGraphAt formation
      corridor hinterior offset hnext
  let localGraph :=
    pointwiseSelectedSourceLocalLayerBoundaryRebaseLocalFaceGraphAt formation
      corridor hinterior offset hnext
  let successorGraph :=
    pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt formation
      corridor hinterior offset hnext
  let adjacency := fun left right : Fin interaction.card =>
    decide (localGraph.Adj (dartAt left) (dartAt right))
  let localPresent := fun slot : Fin interaction.card =>
    decide (formation.annular.RS.edgeOf (dartAt slot) ∈ nextRegion)
  have hinjective : Function.Injective dartAt :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective
      formation corridor hinterior offset hnext
  have hlocalSupport : localGraph.support ⊆ Set.range dartAt := by
    intro dart hdart
    have hcollar : dart ∈
        pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt formation
          corridor hinterior offset hnext :=
      pointwiseSelectedSourceLocalLayerBoundaryRebaseLocalFaceGraphAt_support_subset_collar
        formation corridor hinterior offset hnext hdart
    have hcarrier : dart ∈ interaction := Finset.mem_union_right _ hcollar
    refine ⟨carrierCoordinate interaction ⟨dart, hcarrier⟩, ?_⟩
    simp [dartAt,
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt,
      interaction]
  have hmasked := maskInterfaceExteriorLabelCapCode_exact_code_eq preGraph
    dartAt hinjective removed
    (fun dart => formation.annular.RS.edgeOf dart ∈ preRegion)
    Prod.fst (faceInterfaceIncidenceVertex formation.annular.RS dartAt)
    formation.annular.RS.edgeOf 6
  have hsurvival : (fun dart =>
      formation.annular.RS.edgeOf dart ∈ preRegion ∧
        survivesMask dartAt removed dart) =
      (fun dart => formation.annular.RS.edgeOf dart ∈
        pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCoreRegionAt
          formation corridor hinterior offset hnext) := by
    funext dart
    apply propext
    rw [survivesMask_iff_not_removedByInterfaceMask]
    rw [pointwiseSelected_removedBy_uniformFaceSwitchMask_iff formation corridor
      hinterior offset hnext dart]
    simp [pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCoreRegionAt,
      preRegion]
  have hadded := addInterfaceAdjacencyAndPresence_exact_code_eq
    coreGraph localGraph dartAt hlocalSupport
    (fun dart => formation.annular.RS.edgeOf dart ∈
      pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCoreRegionAt formation
        corridor hinterior offset hnext)
    (fun dart => formation.annular.RS.edgeOf dart ∈ nextRegion)
    Prod.fst (faceInterfaceIncidenceVertex formation.annular.RS dartAt)
    formation.annular.RS.edgeOf adjacency
    (by intro left right; simp [adjacency]) 6
  change addInterfaceAdjacencyAndPresence
      (maskInterfaceExteriorLabelCapCode
        (exactInterfaceExteriorLabelCapCode preGraph dartAt
          (fun dart => formation.annular.RS.edgeOf dart ∈ preRegion)
          Prod.fst (faceInterfaceIncidenceVertex formation.annular.RS dartAt)
          formation.annular.RS.edgeOf 6)
        Prod.fst removed)
      adjacency localPresent =
    exactInterfaceExteriorLabelCapCode successorGraph dartAt
      (fun dart => formation.annular.RS.edgeOf dart ∈ nextRegion)
      Prod.fst (faceInterfaceIncidenceVertex formation.annular.RS dartAt)
      formation.annular.RS.edgeOf 6
  rw [hmasked]
  unfold exactRestrictedInterfaceExteriorLabelCapCode
  rw [pointwiseSelected_restrictedPreRebaseFaceGraph_uniformSwitchMask_eq_core
    formation corridor hinterior offset hnext]
  simp only [hsurvival]
  have hpresent : (fun dart =>
      formation.annular.RS.edgeOf dart ∈
          pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCoreRegionAt
            formation corridor hinterior offset hnext ∨
        formation.annular.RS.edgeOf dart ∈ nextRegion) =
      (fun dart => formation.annular.RS.edgeOf dart ∈ nextRegion) := by
    funext dart
    apply propext
    rw [pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff
      formation corridor hinterior offset hnext]
    simp only [Finset.mem_sdiff]
    tauto
  have hadded' :
      addInterfaceAdjacencyAndPresence
          (exactInterfaceExteriorLabelCapCode coreGraph dartAt
            (fun dart => formation.annular.RS.edgeOf dart ∈
              pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCoreRegionAt
                formation corridor hinterior offset hnext)
            Prod.fst (faceInterfaceIncidenceVertex formation.annular.RS dartAt)
            formation.annular.RS.edgeOf 6)
          adjacency localPresent =
        exactInterfaceExteriorLabelCapCode (coreGraph ⊔ localGraph) dartAt
          (fun dart => formation.annular.RS.edgeOf dart ∈ nextRegion)
          Prod.fst (faceInterfaceIncidenceVertex formation.annular.RS dartAt)
          formation.annular.RS.edgeOf 6 := by
    calc
      _ = exactInterfaceExteriorLabelCapCode (coreGraph ⊔ localGraph) dartAt
          (fun dart =>
            formation.annular.RS.edgeOf dart ∈
                pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCoreRegionAt
                  formation corridor hinterior offset hnext ∨
              formation.annular.RS.edgeOf dart ∈ nextRegion)
          Prod.fst (faceInterfaceIncidenceVertex formation.annular.RS dartAt)
          formation.annular.RS.edgeOf 6 := hadded
      _ = exactInterfaceExteriorLabelCapCode (coreGraph ⊔ localGraph) dartAt
          (fun dart => formation.annular.RS.edgeOf dart ∈ nextRegion)
          Prod.fst (faceInterfaceIncidenceVertex formation.annular.RS dartAt)
          formation.annular.RS.edgeOf 6 := by
        congr 1
  rw [hadded']
  exact congrArg
    (fun graph => exactInterfaceExteriorLabelCapCode graph dartAt
      (fun dart => formation.annular.RS.edgeOf dart ∈ nextRegion)
      Prod.fst (faceInterfaceIncidenceVertex formation.annular.RS dartAt)
      formation.annular.RS.edgeOf 6)
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseCore_sup_local_eq_successor
      formation corridor hinterior offset hnext)

end

end GoertzelV24ClosedWebPointwiseSelectedFaceUniformRecurrence

end Mettapedia.GraphTheory.FourColor
