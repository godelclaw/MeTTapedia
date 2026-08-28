import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedCellRebaseInteractionCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorMaskUpdate
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorTotal
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphSupResidual

/-!
# Exact tracked recurrence on the pointwise-selected interaction carrier

The corrected selected geometry proves directly that the cumulative region
immediately before a boundary rebase and the following terminal-aware region
differ only on four named roles.  This file turns that set locality into the
exact graph-free tracked recurrence used by the rooted rolling machine.

The construction deliberately avoids the historical global shared-edge
selector.  It deletes the selected switch from the old regional graph, calls
the result the unchanged core, and represents the remaining successor edges
by the canonical graph residual.  That residual is proved to live in the
twenty-eight-edge collar, hence in the established forty-nine-edge interaction
carrier.  The generic mask and local-adjacency theorems then give rowwise
equality with the exact successor exterior code.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedTrackedUniformRecurrence

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorMaskUpdate
open GoertzelV24InterfaceDeletionComponentFactorTotal
open GoertzelV24InterfaceDeletionComponentFactorUpdate
open GoertzelV24SimpleGraphSupResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedTrackedUniformRecurrenceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-! ## Literal graphs and coordinates -/

/-- The successor regional tracked graph at an arbitrary cumulative colour
function. -/
noncomputable def pointwiseSelectedSuccessorTrackedGraphForColorAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    SimpleGraph G.edgeSet :=
  regionalTrackedEdgeGraph formation.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior (sourceLocalLayerNextOffset offset hnext))
    color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2

/-- The cumulative tracked graph immediately before the selected boundary
rebase. -/
noncomputable def pointwiseSelectedPreRebaseTrackedGraphForColorAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    SimpleGraph G.edgeSet :=
  regionalTrackedEdgeGraph formation.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
      corridor hinterior offset)
    color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2

/-- Ambient edge represented by a coordinate of the selected interaction
carrier. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Fin (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web corridor hinterior offset hnext).card → G.edgeSet :=
  fun slot ↦
    ((carrierCoordinate
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web corridor hinterior offset hnext)).symm slot).1

theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt_injective
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Function.Injective
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt
        web corridor hinterior offset hnext) := by
  intro left right heq
  apply (carrierCoordinate
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web corridor hinterior offset hnext)).symm.injective
  exact Subtype.ext heq

theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitch_subset_uniformTrackedCarrier
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt web.toFormation
        corridor hinterior offset hnext ⊆
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web corridor hinterior offset hnext := by
  intro edge hedge
  apply Finset.mem_union_right
  apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ edge).2
  exact Or.inl hedge

/-- Boolean mask selecting exactly the four-role switch on the interaction
coordinates. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformSwitchMaskAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Fin (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web corridor hinterior offset hnext).card → Bool :=
  fun slot ↦ decide
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt web
      corridor hinterior offset hnext slot ∈
        pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt web.toFormation
          corridor hinterior offset hnext)

theorem pointwiseSelectedRemovedBy_uniformSwitchMask_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (edge : G.edgeSet) :
    RemovedByInterfaceMask
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt
          web corridor hinterior offset hnext)
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformSwitchMaskAt
          web corridor hinterior offset hnext) edge ↔
      edge ∈ pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt
        web.toFormation corridor hinterior offset hnext := by
  let carrier :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web corridor hinterior offset hnext
  let edgeAt :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt web
      corridor hinterior offset hnext
  let removed :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformSwitchMaskAt web
      corridor hinterior offset hnext
  constructor
  · rintro ⟨slot, hremoved, rfl⟩
    simpa [removed,
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformSwitchMaskAt]
      using hremoved
  · intro hedge
    have hcarrier : edge ∈ carrier :=
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitch_subset_uniformTrackedCarrier
        web corridor hinterior offset hnext hedge
    let slot : Fin carrier.card := carrierCoordinate carrier ⟨edge, hcarrier⟩
    refine ⟨slot, ?_, ?_⟩
    · simp [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformSwitchMaskAt,
        pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt,
        slot, carrier, hedge]
    · simp [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt,
        slot, carrier]

theorem pointwiseSelectedSurvives_uniformSwitchMask_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (edge : G.edgeSet) :
    survivesMask
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt
          web corridor hinterior offset hnext)
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformSwitchMaskAt
          web corridor hinterior offset hnext) edge ↔
      edge ∉ pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt
        web.toFormation corridor hinterior offset hnext := by
  rw [survivesMask_iff_not_removedByInterfaceMask,
    pointwiseSelectedRemovedBy_uniformSwitchMask_iff]

/-! ## Exact core and collar-local residue -/

/-- The unchanged graph is the literal old graph after removing the four
switch vertices. -/
noncomputable def pointwiseSelectedTrackedCoreGraphForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    SimpleGraph G.edgeSet :=
  restrictedByMask
    (pointwiseSelectedPreRebaseTrackedGraphForColorAt web.toFormation corridor
      hinterior offset color pair)
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt web
      corridor hinterior offset hnext)
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformSwitchMaskAt web
      corridor hinterior offset hnext)

theorem pointwiseSelectedTrackedCoreGraphForColorAt_le_successor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    pointwiseSelectedTrackedCoreGraphForColorAt web corridor hinterior offset
        hnext color pair ≤
      pointwiseSelectedSuccessorTrackedGraphForColorAt web.toFormation corridor
        hinterior offset hnext color pair := by
  intro left right hadj
  rcases hadj with ⟨hpre, hleftSurvives, hrightSurvives⟩
  refine ⟨hpre.1, ?_, ?_⟩
  · apply
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
        web.toFormation corridor hinterior offset hnext left ?_).1 hpre.2.1
    exact
      (pointwiseSelectedSurvives_uniformSwitchMask_iff web corridor hinterior
        offset hnext left).1 hleftSurvives
  · apply
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
        web.toFormation corridor hinterior offset hnext right ?_).1 hpre.2.2
    exact
      (pointwiseSelectedSurvives_uniformSwitchMask_iff web corridor hinterior
        offset hnext right).1 hrightSurvives

/-- Exact part of the successor not already supplied by the unchanged core. -/
noncomputable def pointwiseSelectedLocalTrackedGraphForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    SimpleGraph G.edgeSet :=
  supResidual
    (pointwiseSelectedSuccessorTrackedGraphForColorAt web.toFormation corridor
      hinterior offset hnext color pair)
    (pointwiseSelectedTrackedCoreGraphForColorAt web corridor hinterior offset
      hnext color pair)
    (⊥ : SimpleGraph G.edgeSet)

theorem pointwiseSelectedCore_sup_localTracked_eq_successor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    pointwiseSelectedTrackedCoreGraphForColorAt web corridor hinterior offset
        hnext color pair ⊔
      pointwiseSelectedLocalTrackedGraphForColorAt web corridor hinterior offset
        hnext color pair =
      pointwiseSelectedSuccessorTrackedGraphForColorAt web.toFormation corridor
        hinterior offset hnext color pair := by
  have h := sup_sup_supResidual_eq
    (pointwiseSelectedSuccessorTrackedGraphForColorAt web.toFormation corridor
      hinterior offset hnext color pair)
    (pointwiseSelectedTrackedCoreGraphForColorAt web corridor hinterior offset
      hnext color pair)
    (⊥ : SimpleGraph G.edgeSet)
    (pointwiseSelectedTrackedCoreGraphForColorAt_le_successor web corridor
      hinterior offset hnext color pair) bot_le
  simpa [pointwiseSelectedLocalTrackedGraphForColorAt] using h

theorem pointwiseSelectedLocalTrackedGraphForColorAt_support_subset_collar
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    (pointwiseSelectedLocalTrackedGraphForColorAt web corridor hinterior offset
      hnext color pair).support ⊆
      pointwiseSelectedSourceLocalLayerBoundaryRebaseTrackedCollarAt web corridor
        hinterior offset hnext := by
  intro edge hedge
  rcases (SimpleGraph.mem_support _).1 hedge with ⟨other, hadj⟩
  have hresidual := (supResidual_adj
    (pointwiseSelectedSuccessorTrackedGraphForColorAt web.toFormation corridor
      hinterior offset hnext color pair)
    (pointwiseSelectedTrackedCoreGraphForColorAt web corridor hinterior offset
      hnext color pair)
    (⊥ : SimpleGraph G.edgeSet) edge other).1 hadj
  have hwhole := hresidual.1
  have hnotCore := hresidual.2.1
  have hchanged :
      edge ∈ pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt
          web.toFormation corridor hinterior offset hnext ∨
      other ∈ pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt
          web.toFormation corridor hinterior offset hnext := by
    by_contra hnot
    have hedgeNot : edge ∉
        pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt web.toFormation
          corridor hinterior offset hnext := fun h ↦ hnot (Or.inl h)
    have hotherNot : other ∉
        pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt web.toFormation
          corridor hinterior offset hnext := fun h ↦ hnot (Or.inr h)
    apply hnotCore
    refine ⟨?_,
      (pointwiseSelectedSurvives_uniformSwitchMask_iff web corridor hinterior
        offset hnext edge).2 hedgeNot,
      (pointwiseSelectedSurvives_uniformSwitchMask_iff web corridor hinterior
        offset hnext other).2 hotherNot⟩
    refine ⟨hwhole.1, ?_, ?_⟩
    · exact
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
          web.toFormation corridor hinterior offset hnext edge hedgeNot).2
          hwhole.2.1
    · exact
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
          web.toFormation corridor hinterior offset hnext other hotherNot).2
          hwhole.2.2
  apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ edge).2
  rcases hchanged with hedgeChanged | hotherChanged
  · exact Or.inl hedgeChanged
  · exact Or.inr ⟨other, hotherChanged, hwhole.1.1⟩

theorem pointwiseSelectedLocalTrackedGraphForColorAt_support_subset_interaction
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    (pointwiseSelectedLocalTrackedGraphForColorAt web corridor hinterior offset
      hnext color pair).support ⊆
      Set.range
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt
          web corridor hinterior offset hnext) := by
  intro edge hedge
  have hcarrier : edge ∈
      pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web corridor hinterior offset hnext :=
    Finset.mem_union_right _
      (pointwiseSelectedLocalTrackedGraphForColorAt_support_subset_collar web
        corridor hinterior offset hnext color pair hedge)
  refine ⟨carrierCoordinate
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web corridor hinterior offset hnext) ⟨edge, hcarrier⟩, ?_⟩
  simp [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt]

/-! ## Executable recurrence -/

/-- Mask the exact pre-rebase exterior code and add the exact collar-local
successor residue. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedSuccessorRawCodeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    BoundedInterfaceExteriorCode
      (Fin
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
          web corridor hinterior offset hnext).card) :=
  let edgeAt :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt web
      corridor hinterior offset hnext
  let removed :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformSwitchMaskAt web
      corridor hinterior offset hnext
  let preRebase := pointwiseSelectedPreRebaseTrackedGraphForColorAt
    web.toFormation corridor hinterior offset color pair
  let localGraph := pointwiseSelectedLocalTrackedGraphForColorAt web corridor
    hinterior offset hnext color pair
  addInterfaceAdjacency
    (maskInterfaceExteriorCode
      (exactInterfaceExteriorCode preRebase edgeAt) removed)
    (fun left right ↦ by
      classical
      exact decide (localGraph.Adj (edgeAt left) (edgeAt right)))

/-- Rowwise exactness of the corrected selected tracked recurrence. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedSuccessorCodeAt_exact
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    let edgeAt :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt web
        corridor hinterior offset hnext
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedSuccessorRawCodeAt
        web corridor hinterior offset hnext color pair =
      exactInterfaceExteriorCode
        (pointwiseSelectedSuccessorTrackedGraphForColorAt web.toFormation
          corridor hinterior offset hnext color pair) edgeAt := by
  dsimp only
  let edgeAt :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt web
      corridor hinterior offset hnext
  let removed :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformSwitchMaskAt web
      corridor hinterior offset hnext
  let preRebase := pointwiseSelectedPreRebaseTrackedGraphForColorAt
    web.toFormation corridor hinterior offset color pair
  let core := pointwiseSelectedTrackedCoreGraphForColorAt web corridor hinterior
    offset hnext color pair
  let localGraph := pointwiseSelectedLocalTrackedGraphForColorAt web corridor
    hinterior offset hnext color pair
  let localAdjacency :
      Fin
          (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
            web corridor hinterior offset hnext).card →
        Fin
          (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
            web corridor hinterior offset hnext).card → Bool :=
    fun left right ↦ by
      classical
      exact decide (localGraph.Adj (edgeAt left) (edgeAt right))
  change addInterfaceAdjacency
      (maskInterfaceExteriorCode (exactInterfaceExteriorCode preRebase edgeAt)
        removed)
      localAdjacency =
    exactInterfaceExteriorCode
      (pointwiseSelectedSuccessorTrackedGraphForColorAt web.toFormation corridor
        hinterior offset hnext color pair) edgeAt
  rw [maskInterfaceExteriorCode_exact_code_eq preRebase edgeAt
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt_injective
      web corridor hinterior offset hnext) removed]
  change addInterfaceAdjacency (exactInterfaceExteriorCode core edgeAt)
      localAdjacency = _
  rw [addInterfaceAdjacency_exact_code_eq core localGraph edgeAt
    (pointwiseSelectedLocalTrackedGraphForColorAt_support_subset_interaction web
      corridor hinterior offset hnext color pair) localAdjacency
    (fun left right ↦ by simp [localAdjacency])]
  rw [pointwiseSelectedCore_sup_localTracked_eq_successor web corridor
    hinterior offset hnext color pair]

end

end GoertzelV24ClosedWebPointwiseSelectedTrackedUniformRecurrence

end Mettapedia.GraphTheory.FourColor
