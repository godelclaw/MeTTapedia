import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedCellNativeFactorization
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceUniformRecurrence

/-!
# Exact selected facial update before the boundary rebase

The generic rooted machine lifts the current twenty-four-slot Cell/seam face
table into the complete forty-eight-slot interaction carrier.  This file
proves that lift exact for the corrected pointwise-selected corridor geometry.
For every arbitrary compatible cumulative prefix and positive literal Cell,
the guarded graph-free update succeeds and returns the canonical cap-six code
of the literal prefix-plus-Cell region.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedFacePreRebaseExact

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24ClosedWebPointwiseSelectedCellFiniteSupportLetter
open GoertzelV24ClosedWebPointwiseSelectedCellNativeFactorization
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteEdgeState
open GoertzelV24ClosedWebPointwiseSelectedFaceUniformRecurrence
open GoertzelV24ClosedWebPointwiseSelectedRootedInteractionState
open GoertzelV24CorridorProfile
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFactorUpdate
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24RotationFaceRegionalDartCarrier
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFacePreRebaseExactEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-! ## Exact local Cell/seam table -/

/-- The two prefix-independent facial graph factors of one selected Cell. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialFaceLocalGraphAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    SimpleGraph formation.annular.RS.D :=
  faceRegionalDartGraph formation.annular.RS
      (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset) ⊔
    pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt formation
      corridor hinterior offset

/-- Executable selected local adjacency on the dependent current carrier. -/
noncomputable def
    pointwiseSelectedSourceLocalLayerSerialFaceLocalAdjacencyAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6) :
    let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt
      formation corridor hinterior offset hcell
    Fin code.vertexCount.val → Fin code.vertexCount.val → Bool :=
  let code := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt
    formation corridor hinterior offset hcell
  fun left right => by
    classical
    exact decide (((code.graph false) ⊔ (code.graph true)).Adj left right)

theorem pointwiseSelectedSourceLocalLayerSerialFaceLocalGraph_support_subset_carrier
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    (pointwiseSelectedSourceLocalLayerSerialFaceLocalGraphAt formation corridor
      hinterior offset).support ⊆
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset : Set formation.annular.RS.D) := by
  intro dart hdart
  rcases hdart with ⟨neighbor, hadj⟩
  change
    (faceRegionalDartGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
          hinterior offset) ⊔
      pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt formation
        corridor hinterior offset).Adj dart neighbor at hadj
  rw [SimpleGraph.sup_adj] at hadj
  rcases hadj with hcell | hseam
  · exact
      pointwiseSelectedSourceLocalLayerCellFaceDartGraph_support_subset_transitionCarrier
        formation corridor hinterior offset ⟨neighbor, hcell⟩
  · exact
      pointwiseSelectedSourceLocalLayerFaceDartSeam_support_subset_transitionCarrier
        formation corridor hinterior offset ⟨neighbor, hseam⟩

theorem pointwiseSelectedSourceLocalLayerSerialFaceLocalGraph_support_subset_range
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    let carrier :=
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset
    let dartAt := fun slot : Fin carrier.card =>
      ((carrierCoordinate carrier).symm slot).1
    (pointwiseSelectedSourceLocalLayerSerialFaceLocalGraphAt formation corridor
      hinterior offset).support ⊆ Set.range dartAt := by
  dsimp only
  intro dart hdart
  let carrier :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
      corridor hinterior offset
  have hcarrier : dart ∈ carrier :=
    pointwiseSelectedSourceLocalLayerSerialFaceLocalGraph_support_subset_carrier
      formation corridor hinterior offset hdart
  refine ⟨carrierCoordinate carrier ⟨dart, hcarrier⟩, ?_⟩
  simp [carrier]

/-- The selected Boolean Cell/seam row is exactly the literal local facial
graph on all live current coordinates. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceLocalAdjacencyAt_exact
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
      hinterior offset).card ≤ 6)
    (left right : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
        corridor hinterior offset).card) :
    pointwiseSelectedSourceLocalLayerSerialFaceLocalAdjacencyAt formation
        corridor hinterior offset hcell left right = true ↔
      let carrier :=
        pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
          corridor hinterior offset
      let dartAt := fun slot : Fin carrier.card =>
        ((carrierCoordinate carrier).symm slot).1
      (pointwiseSelectedSourceLocalLayerSerialFaceLocalGraphAt formation corridor
        hinterior offset).Adj (dartAt left) (dartAt right) := by
  classical
  let carrier :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
      corridor hinterior offset
  let localCode :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt formation
      corridor hinterior offset hcell
  let first : {dart // dart ∈ carrier} :=
    (carrierCoordinate carrier).symm left
  let second : {dart // dart ∈ carrier} :=
    (carrierCoordinate carrier).symm right
  have hcellIff :
      (localCode.graph false).Adj left right ↔
        (faceRegionalDartGraph formation.annular.RS
          (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
            hinterior offset)).Adj first.1 second.1 := by
    have h := boundedCarrierGraphFamilyCode_adj_iff carrier 24 0
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
        formation corridor hinterior offset hcell)
      (fun index => Fin.elim0 index)
      (fun seam => if seam then
        pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt formation
          corridor hinterior offset
      else
        faceRegionalDartGraph formation.annular.RS
          (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
            hinterior offset))
      false first second
    simpa [localCode,
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt, first,
      second] using h
  have hseamIff :
      (localCode.graph true).Adj left right ↔
        (pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt formation
          corridor hinterior offset).Adj first.1 second.1 := by
    have h := boundedCarrierGraphFamilyCode_adj_iff carrier 24 0
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
        formation corridor hinterior offset hcell)
      (fun index => Fin.elim0 index)
      (fun seam => if seam then
        pointwiseSelectedSourceLocalLayerSerialTerminalFaceDartSeamAt formation
          corridor hinterior offset
      else
        faceRegionalDartGraph formation.annular.RS
          (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
            hinterior offset))
      true first second
    simpa [localCode,
      pointwiseSelectedSourceLocalLayerSerialFaceTransitionCodeAt, first,
      second] using h
  change decide (((localCode.graph false) ⊔ (localCode.graph true)).Adj
    left right) = true ↔ _
  rw [decide_eq_true_eq, SimpleGraph.sup_adj,
    pointwiseSelectedSourceLocalLayerSerialFaceLocalGraphAt,
    SimpleGraph.sup_adj]
  exact or_congr hcellIff hseamIff

/-! ## Exact lift to the complete interaction carrier -/

/-- The native selected local factor reads precisely the selected Cell/seam
Boolean adjacency row. -/
theorem pointwiseSelectedSourceLocalLayerSerialPhysicalFaceLocalAdjacencyAt_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor : G.edgeSet → Color)
    (hprefix : ∀ step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt
        web.toFormation corridor hinterior offset step) ≠ 0)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset)
    (left right : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt
        web.toFormation corridor hinterior offset).card) :
    let state :=
      pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
    let localFactor :=
      (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring).2.2
    sourceLocalLayerSerialCellPhysicalFaceLocalAdjacency
        state.toSourceLocalLayerSerialColoredCumulativeState localFactor (by rfl)
        left right =
      pointwiseSelectedSourceLocalLayerSerialFaceLocalAdjacencyAt web.toFormation
        corridor hinterior offset hcell left right := by
  classical
  simp only
    [pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt,
      pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt,
      pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolLocalFactorAt,
      pointwiseSelectedSourceLocalLayerSerialCellFiniteSupportLetterAt,
      sourceLocalLayerSerialCellPhysicalFaceLocalAdjacency]
  simp only [ofGraphFamilyCode_toGraph]
  rfl

theorem
    pointwiseSelectedSourceLocalLayerSerialRootedInteractionFaceLocalAdjacencyAt_eq_true_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor : G.edgeSet → Color)
    (hprefix : ∀ step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt
        web.toFormation corridor hinterior offset step) ≠ 0)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset)
    (hcount :
      (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
        ).faceCapSix.vertexCount =
      (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring).2.2.faceCode.vertexCount)
    (left right : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        web.toFormation corridor hinterior offset hnext).card) :
    sourceLocalLayerSerialRootedInteractionFaceLocalAdjacency
        (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
          web corridor hinterior offset hnext hcell prefixColor hprefix)
        (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
          web corridor hinterior offset hnext hcell prefixColor hprefix
            cellColoring).2.2
        hcount left right = true ↔
      (pointwiseSelectedSourceLocalLayerSerialFaceLocalGraphAt web.toFormation
        corridor hinterior offset).Adj
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
          web.toFormation corridor hinterior offset hnext left)
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
          web.toFormation corridor hinterior offset hnext right) := by
  classical
  let state :=
    pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt web
      corridor hinterior offset hnext hcell prefixColor hprefix
  let factor :=
    (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt web
      corridor hinterior offset hnext hcell prefixColor hprefix cellColoring).2.2
  let current :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation
      corridor hinterior offset
  let extra := pointwiseSelectedSourceLocalLayerSerialFaceLocalGraphAt
    web.toFormation corridor hinterior offset
  let oldVertex := fun slot : Fin current.card =>
    ((carrierCoordinate current).symm slot).1
  let newVertex :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
      web.toFormation corridor hinterior offset hnext
  have hcoordinate : ∀ old,
      newVertex (state.faceCurrentCoordinate old) = oldVertex old := by
    intro old
    exact
      pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt_faceCurrentDart
        web corridor hinterior offset hnext hcell prefixColor hprefix old
  have hnewInjective : Function.Injective newVertex :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective
      web.toFormation corridor hinterior offset hnext
  have hsupport : extra.support ⊆ Set.range oldVertex :=
    pointwiseSelectedSourceLocalLayerSerialFaceLocalGraph_support_subset_range
      web.toFormation corridor hinterior offset
  have hadjacency : ∀ oldLeft oldRight,
      sourceLocalLayerSerialCellPhysicalFaceLocalAdjacency
          state.toSourceLocalLayerSerialColoredCumulativeState factor hcount
          oldLeft oldRight = true ↔
        extra.Adj (oldVertex oldLeft) (oldVertex oldRight) := by
    intro oldLeft oldRight
    change Fin current.card at oldLeft oldRight
    have hcountRfl : hcount = (by rfl) := Subsingleton.elim _ _
    rw [hcountRfl]
    rw [pointwiseSelectedSourceLocalLayerSerialPhysicalFaceLocalAdjacencyAt_eq
      web corridor hinterior offset hnext hcell prefixColor hprefix cellColoring
        oldLeft oldRight]
    exact
      pointwiseSelectedSourceLocalLayerSerialFaceLocalAdjacencyAt_exact
        web.toFormation corridor hinterior offset hcell oldLeft oldRight
  exact liftInterfaceAdjacency_eq_true_iff extra oldVertex newVertex
    state.faceCurrentCoordinate hcoordinate hnewInjective hsupport
    (sourceLocalLayerSerialCellPhysicalFaceLocalAdjacency
      state.toSourceLocalLayerSerialColoredCumulativeState factor hcount)
    hadjacency left right

/-- Lifted selected Cell activity is exactly literal Cell membership on the
complete interaction carrier. -/
theorem
    pointwiseSelectedSourceLocalLayerSerialRootedInteractionFaceLocalPresenceAt_eq_true_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor : G.edgeSet → Color)
    (hprefix : ∀ step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt
        web.toFormation corridor hinterior offset step) ≠ 0)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset)
    (slot : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        web.toFormation corridor hinterior offset hnext).card) :
    sourceLocalLayerSerialRootedInteractionFaceLocalPresence
        (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
          web corridor hinterior offset hnext hcell prefixColor hprefix)
        (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
          web corridor hinterior offset hnext hcell prefixColor hprefix
            cellColoring).2.2 slot = true ↔
      web.annular.RS.edgeOf
          (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
            web.toFormation corridor hinterior offset hnext slot) ∈
        pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
          hinterior offset := by
  classical
  let state :=
    pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt web
      corridor hinterior offset hnext hcell prefixColor hprefix
  let factor :=
    (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt web
      corridor hinterior offset hnext hcell prefixColor hprefix cellColoring).2.2
  let current :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation
      corridor hinterior offset
  let oldVertex := fun old : Fin current.card =>
    ((carrierCoordinate current).symm old).1
  let newVertex :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
      web.toFormation corridor hinterior offset hnext
  have hcoordinate : ∀ old,
      newVertex (state.faceCurrentCoordinate old) = oldVertex old := by
    intro old
    exact
      pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt_faceCurrentDart
        web corridor hinterior offset hnext hcell prefixColor hprefix old
  have hnewInjective : Function.Injective newVertex :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective
      web.toFormation corridor hinterior offset hnext
  have hpresent : ∀ old,
      factor.faceEdgeState.cellPresent
          (Fin.castLE
            (Nat.le_of_lt_succ state.faceCapSix.vertexCount.isLt) old) = true ↔
        web.annular.RS.edgeOf (oldVertex old) ∈
          pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
            hinterior offset := by
    intro old
    change Fin current.card at old
    have hslot :
        Fin.castLE
            (Nat.le_of_lt_succ state.faceCapSix.vertexCount.isLt) old =
          pointwiseSelectedSourceLocalLayerSerialFaceTransitionSlotAt
            web.toFormation corridor hinterior offset hcell
            ((carrierCoordinate current).symm old) := by
      apply Fin.ext
      change old.val =
        (carrierCoordinate current
          ((carrierCoordinate current).symm (Fin.cast (by rfl) old))).val
      rw [Equiv.apply_symm_apply]
      rfl
    change
      (pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt
        web.toFormation corridor hinterior offset hcell).cellPresent
          (Fin.castLE
            (Nat.le_of_lt_succ state.faceCapSix.vertexCount.isLt) old) = true ↔
        web.annular.RS.edgeOf (oldVertex old) ∈
          pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
            hinterior offset
    rw [hslot,
      pointwiseSelectedSourceLocalLayerSerialFaceFiniteEdgeStateAt_cellPresent_iff]
  have hcovered : ∀ new,
      web.annular.RS.edgeOf (newVertex new) ∈
          pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
            hinterior offset →
        ∃ old, oldVertex old = newVertex new := by
    intro new hcellMem
    have hcurrent : newVertex new ∈ current := by
      apply Finset.mem_union_left
      exact (mem_dartsOnEdges_iff web.annular.RS _ _).2 hcellMem
    refine ⟨carrierCoordinate current ⟨newVertex new, hcurrent⟩, ?_⟩
    simp [oldVertex]
  exact liftInterfacePresence_eq_true_iff_of_exact oldVertex newVertex
    state.faceCurrentCoordinate hcoordinate hnewInjective
    (fun old => factor.faceEdgeState.cellPresent
      (Fin.castLE
        (Nat.le_of_lt_succ state.faceCapSix.vertexCount.isLt) old))
    (fun dart => web.annular.RS.edgeOf dart ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
        hinterior offset)
    hpresent hcovered slot

/-- The selected Cell/seam local graph is supported on the complete
forty-eight-coordinate interaction carrier. -/
theorem
    pointwiseSelectedSourceLocalLayerSerialFaceLocalGraph_support_subset_interaction_range
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
    (pointwiseSelectedSourceLocalLayerSerialFaceLocalGraphAt formation corridor
      hinterior offset).support ⊆ Set.range dartAt := by
  dsimp only
  intro dart hdart
  let current :=
    pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt formation
      corridor hinterior offset
  let interaction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      formation corridor hinterior offset hnext
  have hcurrent : dart ∈ current :=
    pointwiseSelectedSourceLocalLayerSerialFaceLocalGraph_support_subset_carrier
      formation corridor hinterior offset hdart
  have hinteraction : dart ∈ interaction := Finset.mem_union_left _ hcurrent
  refine ⟨carrierCoordinate interaction ⟨dart, hinteraction⟩, ?_⟩
  simp [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt,
    interaction]

/-! ## Exact pre-rebase state -/

/-- For every arbitrary compatible prefix and positive literal selected Cell,
the graph-free enlarged update is exactly the canonical pre-rebase facial
code. -/
theorem
    pointwiseSelectedSourceLocalLayerSerialRootedInteractionFacePreRebaseStateAt_code_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor : G.edgeSet → Color)
    (hprefix : ∀ step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt
        web.toFormation corridor hinterior offset step) ≠ 0)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset)
    (hcount :
      (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
        ).faceCapSix.vertexCount =
      (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring).2.2.faceCode.vertexCount) :
    (sourceLocalLayerSerialRootedInteractionFacePreRebaseState
      (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web corridor hinterior offset hnext hcell prefixColor hprefix)
      (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring).2.2
      hcount).code () =
    (pointwiseSelectedSourceLocalLayerSerialFaceInteractionPreRebaseStateAt
      web.toFormation corridor hinterior offset hnext hcell).code () := by
  classical
  let state :=
    pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt web
      corridor hinterior offset hnext hcell prefixColor hprefix
  let factor :=
    (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt web
      corridor hinterior offset hnext hcell prefixColor hprefix cellColoring).2.2
  let interaction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      web.toFormation corridor hinterior offset hnext
  let dartAt :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
      web.toFormation corridor hinterior offset hnext
  let prefixRegion :=
    pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation
      corridor hinterior offset
  let cellRegion := pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
    corridor hinterior offset
  let prefixGraph := faceRegionalDartGraph web.annular.RS prefixRegion
  let localGraph := pointwiseSelectedSourceLocalLayerSerialFaceLocalGraphAt
    web.toFormation corridor hinterior offset
  let adjacency :=
    sourceLocalLayerSerialRootedInteractionFaceLocalAdjacency state factor hcount
  let presence :=
    sourceLocalLayerSerialRootedInteractionFaceLocalPresence state factor
  have hadjacency : ∀ left right,
      adjacency left right = true ↔
        localGraph.Adj (dartAt left) (dartAt right) := by
    intro left right
    exact
      pointwiseSelectedSourceLocalLayerSerialRootedInteractionFaceLocalAdjacencyAt_eq_true_iff
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring hcount left right
  have hpresence : presence = fun slot =>
      decide (web.annular.RS.edgeOf (dartAt slot) ∈ cellRegion) := by
    funext slot
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact
      pointwiseSelectedSourceLocalLayerSerialRootedInteractionFaceLocalPresenceAt_eq_true_iff
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring slot
  have hupdate := addInterfaceAdjacencyAndPresence_exact_code_eq
    prefixGraph localGraph dartAt
    (pointwiseSelectedSourceLocalLayerSerialFaceLocalGraph_support_subset_interaction_range
      web.toFormation corridor hinterior offset hnext)
    (fun dart => web.annular.RS.edgeOf dart ∈ prefixRegion)
    (fun dart => web.annular.RS.edgeOf dart ∈ cellRegion)
    Prod.fst (faceInterfaceIncidenceVertex web.annular.RS dartAt)
    web.annular.RS.edgeOf adjacency hadjacency 6
  change addInterfaceAdjacencyAndPresence
      (exactInterfaceExteriorLabelCapCode prefixGraph dartAt
        (fun dart => web.annular.RS.edgeOf dart ∈ prefixRegion)
        Prod.fst (faceInterfaceIncidenceVertex web.annular.RS dartAt)
        web.annular.RS.edgeOf 6)
      adjacency presence =
    exactFaceInterfaceExteriorLabelCapCode web.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
        web.toFormation corridor hinterior offset)
      dartAt 6
  rw [hpresence]
  unfold exactFaceInterfaceExteriorLabelCapCode
  rw [pointwiseSelectedSourceLocalLayerSerialPreRebaseFaceDartGraph_eq_three_factor
    web.toFormation corridor hinterior offset, sup_assoc]
  rw [← pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt_union_cell
    web.toFormation corridor hinterior offset]
  simpa only [prefixGraph, localGraph, prefixRegion, cellRegion,
    pointwiseSelectedSourceLocalLayerSerialFaceLocalGraphAt,
    Finset.mem_union] using hupdate

/-- The guarded selected facial interaction update succeeds on every literal
source Cell and returns the canonical exact pre-rebase state. -/
theorem
    pointwiseSelectedSourceLocalLayerSerialRootedInteractionFacePreRebaseState?_at
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor : G.edgeSet → Color)
    (hprefix : ∀ step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt
        web.toFormation corridor hinterior offset step) ≠ 0)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset) :
    let state :=
      pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
    let factor :=
      (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring).2.2
    sourceLocalLayerSerialRootedInteractionFacePreRebaseState? state factor =
      some
        (pointwiseSelectedSourceLocalLayerSerialFaceInteractionPreRebaseStateAt
          web.toFormation corridor hinterior offset hnext hcell) := by
  classical
  let state :=
    pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt web
      corridor hinterior offset hnext hcell prefixColor hprefix
  let factor :=
    (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt web
      corridor hinterior offset hnext hcell prefixColor hprefix cellColoring).2.2
  let expected :=
    pointwiseSelectedSourceLocalLayerSerialFaceInteractionPreRebaseStateAt
      web.toFormation corridor hinterior offset hnext hcell
  change sourceLocalLayerSerialRootedInteractionFacePreRebaseState? state factor =
    some expected
  unfold sourceLocalLayerSerialRootedInteractionFacePreRebaseState?
  split <;> rename_i hcount
  · congr 1
    unfold sourceLocalLayerSerialRootedInteractionFacePreRebaseState
    congr 1
    funext family
    exact
      pointwiseSelectedSourceLocalLayerSerialRootedInteractionFacePreRebaseStateAt_code_eq
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring hcount
  · exfalso
    apply hcount
    rfl

end

end GoertzelV24ClosedWebPointwiseSelectedFacePreRebaseExact

end Mettapedia.GraphTheory.FourColor
