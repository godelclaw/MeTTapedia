import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedCellNativeFactorization
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedRebaseFactor

/-!
# Exact selected tracked update before the boundary rebase

The generic rooted machine lifts the current twenty-one-slot Cell/seam table
into the complete forty-nine-slot interaction carrier.  This file proves that
lift exact for the corrected pointwise-selected corridor geometry.  For every
arbitrary compatible cumulative prefix and positive literal Cell, the guarded
graph-free update succeeds and returns the canonical exterior code of the
literal prefix-plus-Cell region.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedTrackedPreRebaseExact

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteBoolSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedBoolColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24ClosedWebLocalLayerSerialRootedPreRebaseState
open GoertzelV24ClosedWebPointwiseSelectedCellNativeFactorization
open GoertzelV24ClosedWebPointwiseSelectedRootedInteractionState
open GoertzelV24ClosedWebPointwiseSelectedTrackedRebaseFactor
open GoertzelV24ClosedWebPointwiseSelectedTrackedUniformRecurrence
open GoertzelV24CorridorProfile
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorUpdate
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedTrackedPreRebaseExactEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-! ## Exact local Cell/seam table -/

/-- The two prefix-independent tracked graph factors of one selected Cell. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialTrackedLocalGraphAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet -> Color) (pair : TrackedColorPair) :
    SimpleGraph G.edgeSet :=
  regionalTrackedEdgeGraph formation.annular.RS
      (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset)
      color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2 ⊔
    pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt formation
      corridor hinterior offset color (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2

/-- Executable selected local adjacency on the dependent current carrier. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialTrackedLocalAdjacencyAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card <= 6)
    (color : G.edgeSet -> Color) (pair : TrackedColorPair) :
    let code := pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt
      web corridor hinterior offset hcell color
    Fin code.vertexCount.val -> Fin code.vertexCount.val -> Bool :=
  let code := pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt
    web corridor hinterior offset hcell color
  fun left right => by
    classical
    exact decide (((code.graph (pair, false)) ⊔
      (code.graph (pair, true))).Adj left right)

theorem pointwiseSelectedSourceLocalLayerSerialTrackedLocalGraphAt_support_subset_carrier
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet -> Color) (pair : TrackedColorPair) :
    (pointwiseSelectedSourceLocalLayerSerialTrackedLocalGraphAt formation
      corridor hinterior offset color pair).support ⊆
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset : Set G.edgeSet) := by
  intro edge hedge
  rcases hedge with ⟨neighbor, hadj⟩
  change
    (regionalTrackedEdgeGraph formation.annular.RS
          (pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
            hinterior offset)
          color (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2 ⊔
      pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt formation
        corridor hinterior offset color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Adj edge neighbor at hadj
  rw [SimpleGraph.sup_adj] at hadj
  rcases hadj with hcell | hseam
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hcell.2.1)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt_support_subset_outgoingCarrier
        formation corridor hinterior offset color
          (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
          ⟨neighbor, hseam⟩))

theorem pointwiseSelectedSourceLocalLayerSerialTrackedLocalGraphAt_support_subset_range
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet -> Color) (pair : TrackedColorPair) :
    let carrier :=
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset
    let edgeAt := fun slot : Fin carrier.card =>
      ((carrierCoordinate carrier).symm slot).1
    (pointwiseSelectedSourceLocalLayerSerialTrackedLocalGraphAt formation
      corridor hinterior offset color pair).support ⊆ Set.range edgeAt := by
  dsimp only
  intro edge hedge
  let carrier :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt formation
      corridor hinterior offset
  have hcarrier : edge ∈ carrier :=
    pointwiseSelectedSourceLocalLayerSerialTrackedLocalGraphAt_support_subset_carrier
      formation corridor hinterior offset color pair hedge
  refine ⟨carrierCoordinate carrier ⟨edge, hcarrier⟩, ?_⟩
  simp [carrier]

/-- The selected Boolean Cell/seam row is exactly the literal local tracked
graph on all live current coordinates. -/
theorem pointwiseSelectedSourceLocalLayerSerialTrackedLocalAdjacencyAt_exact
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card <= 6)
    (color : G.edgeSet -> Color) (pair : TrackedColorPair)
    (left right : Fin
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        web.toFormation corridor hinterior offset).card) :
    pointwiseSelectedSourceLocalLayerSerialTrackedLocalAdjacencyAt web corridor
        hinterior offset hcell color pair left right = true ↔
      let carrier :=
        pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
          web.toFormation corridor hinterior offset
      let edgeAt := fun slot : Fin carrier.card =>
        ((carrierCoordinate carrier).symm slot).1
      (pointwiseSelectedSourceLocalLayerSerialTrackedLocalGraphAt web.toFormation
        corridor hinterior offset color pair).Adj (edgeAt left) (edgeAt right) := by
  classical
  let carrier :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      web.toFormation corridor hinterior offset
  let localCode :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt web
      corridor hinterior offset hcell color
  let first : {edge // edge ∈ carrier} :=
    (carrierCoordinate carrier).symm left
  let second : {edge // edge ∈ carrier} :=
    (carrierCoordinate carrier).symm right
  have hcellIff :
      (localCode.graph (pair, false)).Adj left right ↔
        (regionalTrackedEdgeGraph web.annular.RS
          (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
            corridor hinterior offset)
          color (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2).Adj first.1 second.1 := by
    have h := boundedCarrierGraphFamilyCode_adj_iff carrier 21 5
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
        web corridor hinterior offset hcell)
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionPointAt
        web.toFormation corridor hinterior offset)
      (fun factor : TrackedColorPair × Bool => if factor.2 then
        pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt
          web.toFormation corridor hinterior offset color
            (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2
      else regionalTrackedEdgeGraph web.annular.RS
        (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
          hinterior offset) color (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2)
      (pair, false) first second
    simpa [localCode,
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt,
      first, second] using h
  have hseamIff :
      (localCode.graph (pair, true)).Adj left right ↔
        (pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt
          web.toFormation corridor hinterior offset color
          (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2).Adj first.1 second.1 := by
    have h := boundedCarrierGraphFamilyCode_adj_iff carrier 21 5
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
        web corridor hinterior offset hcell)
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionPointAt
        web.toFormation corridor hinterior offset)
      (fun factor : TrackedColorPair × Bool => if factor.2 then
        pointwiseSelectedSourceLocalLayerSerialTerminalTrackedSeamAt
          web.toFormation corridor hinterior offset color
            (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2
      else regionalTrackedEdgeGraph web.annular.RS
        (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
          hinterior offset) color (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2)
      (pair, true) first second
    simpa [localCode,
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt,
      first, second] using h
  change decide (((localCode.graph (pair, false)) ⊔
    (localCode.graph (pair, true))).Adj left right) = true ↔ _
  rw [decide_eq_true_eq, SimpleGraph.sup_adj,
    pointwiseSelectedSourceLocalLayerSerialTrackedLocalGraphAt,
    SimpleGraph.sup_adj]
  exact or_congr hcellIff hseamIff

/-- Splicing compatible Cell colours changes no tracked edge of the
terminal-aware prefix region. -/
theorem pointwiseSelectedRegionalTrackedEdgeGraph_spliced_eq_prefix
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (prefixColor cellColor : G.edgeSet -> Color)
    (hcompatible :
      PointwiseSelectedSourceLocalLayerSerialTerminalCellColorsCompatibleAt
        formation corridor hinterior offset prefixColor cellColor)
    (first second : Color) :
    regionalTrackedEdgeGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior offset)
        (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt formation
          corridor hinterior offset prefixColor cellColor) first second =
      regionalTrackedEdgeGraph formation.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior offset) prefixColor first second := by
  ext left right
  simp only [regionalTrackedEdgeGraph, RotationSystem.trackedEdgeGraph]
  constructor
  · rintro ⟨⟨hadj, hleftTracked, hrightTracked⟩, hleft, hright⟩
    exact ⟨⟨hadj,
      (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_prefix_of_mem_terminalInput
        formation corridor hinterior offset prefixColor cellColor hcompatible
          hleft) ▸ hleftTracked,
      (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_prefix_of_mem_terminalInput
        formation corridor hinterior offset prefixColor cellColor hcompatible
          hright) ▸ hrightTracked⟩, hleft, hright⟩
  · rintro ⟨⟨hadj, hleftTracked, hrightTracked⟩, hleft, hright⟩
    exact ⟨⟨hadj,
      (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_prefix_of_mem_terminalInput
        formation corridor hinterior offset prefixColor cellColor hcompatible
          hleft).symm ▸ hleftTracked,
      (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_prefix_of_mem_terminalInput
        formation corridor hinterior offset prefixColor cellColor hcompatible
          hright).symm ▸ hrightTracked⟩, hleft, hright⟩

/-! ## Exact lift to the complete interaction carrier -/

/-- The native selected physical factor reads precisely the selected
Cell/seam Boolean adjacency row. -/
theorem pointwiseSelectedSourceLocalLayerSerialPhysicalTrackedLocalAdjacencyAt_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card <= 6)
    (prefixColor : G.edgeSet -> Color)
    (hprefix : forall step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt
        web.toFormation corridor hinterior offset step) ≠ 0)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset)
    (hcount :
      (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
        ).trackedExterior.vertexCount =
      (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring).2.2.trackedGeometry.vertexCount)
    (pair : TrackedColorPair) :
    sourceLocalLayerSerialRootedTrackedLocalAdjacency
        (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
          web corridor hinterior offset hnext hcell prefixColor hprefix
          ).toSourceLocalLayerSerialRootedCumulativeState
        (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
          web corridor hinterior offset hnext hcell prefixColor hprefix
            cellColoring).2.2
        hcount pair =
      pointwiseSelectedSourceLocalLayerSerialTrackedLocalAdjacencyAt web corridor
        hinterior offset hcell
        (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
          corridor hinterior offset prefixColor
          (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
            corridor hinterior offset cellColoring)) pair := by
  classical
  let state :=
    pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt web
      corridor hinterior offset hnext hcell prefixColor hprefix
  let factor :=
    (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt web
      corridor hinterior offset hnext hcell prefixColor hprefix cellColoring).2.2
  let cellColor := pointwiseSelectedSourceLocalLayerCellLiteralColorAt
    web.toFormation corridor hinterior offset cellColoring
  let spliced := pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
    web.toFormation corridor hinterior offset prefixColor cellColor
  let geometry :=
    pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt web corridor
      hinterior offset hcell
  let oldCode :=
    pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
      corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
          web.toFormation corridor hinterior offset) prefixColor
  let cellCode :=
    pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
      corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation corridor
          hinterior offset) cellColor
  let reconstructed :=
    pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColors geometry
      oldCode cellCode
  let native := sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry
    factor.trackedGeometry state.colorCode factor.trackedCellColor
  let source := pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCodeForColorAt
    web corridor hinterior offset hcell spliced
  have hgeometry : factor.trackedGeometry = ofGraphFamilyCode geometry := by
    rfl
  have holdCode : state.colorCode = oldCode := by
    rfl
  have hcellCode : factor.trackedCellColor = cellCode := by
    rfl
  funext left right
  cases hcount
  change Fin native.vertexCount.val at left right
  have hnative (seam : Bool) :
      native.toGraph (pair, seam) = reconstructed.graph (pair, seam) := by
    dsimp only [native]
    cases hgeometry
    cases holdCode
    cases hcellCode
    exact sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry_toGraph
      geometry oldCode cellCode (pair, seam)
  have hsource (seam : Bool) :
      reconstructed.graph (pair, seam) = source.graph (pair, seam) := by
    dsimp only [reconstructed, source, geometry, oldCode, cellCode, spliced,
      cellColor]
    exact
      pointwiseSelectedSourceLocalLayerSerialTrackedCodeOfFiniteColorsAt_graph_eq
        web corridor hinterior offset hcell prefixColor
          (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
            corridor hinterior offset cellColoring) (pair, seam)
  have hgraph (seam : Bool) :
      native.toGraph (pair, seam) = source.graph (pair, seam) := by
    exact (hnative seam).trans (hsource seam)
  change decide ((native.toGraph (pair, false) ⊔
      native.toGraph (pair, true)).Adj left right) =
    decide ((source.graph (pair, false) ⊔ source.graph (pair, true)).Adj
      left right)
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, SimpleGraph.sup_adj]
  exact or_congr
    (Eq.to_iff (congrArg (fun graph => graph.Adj left right) (hgraph false)))
    (Eq.to_iff (congrArg (fun graph => graph.Adj left right) (hgraph true)))

/-- The lifted native table is exactly the literal selected Cell/seam graph
on the complete interaction carrier. -/
theorem
    pointwiseSelectedSourceLocalLayerSerialRootedInteractionLocalAdjacencyAt_eq_true_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card <= 6)
    (prefixColor : G.edgeSet -> Color)
    (hprefix : forall step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt
        web.toFormation corridor hinterior offset step) ≠ 0)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset)
    (hcount :
      (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
        ).trackedExterior.vertexCount =
      (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring).2.2.trackedGeometry.vertexCount)
    (pair : TrackedColorPair)
    (left right : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
        web corridor hinterior offset hnext).card) :
    sourceLocalLayerSerialRootedInteractionLocalAdjacency
        (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
          web corridor hinterior offset hnext hcell prefixColor hprefix)
        (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
          web corridor hinterior offset hnext hcell prefixColor hprefix
            cellColoring).2.2
        hcount pair left right = true ↔
      (pointwiseSelectedSourceLocalLayerSerialTrackedLocalGraphAt web.toFormation
        corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
          corridor hinterior offset prefixColor
          (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
            corridor hinterior offset cellColoring)) pair).Adj
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt
          web corridor hinterior offset hnext left)
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt
          web corridor hinterior offset hnext right) := by
  classical
  let state :=
    pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt web
      corridor hinterior offset hnext hcell prefixColor hprefix
  let factor :=
    (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt web
      corridor hinterior offset hnext hcell prefixColor hprefix cellColoring).2.2
  let current :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      web.toFormation corridor hinterior offset
  let spliced := pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
    web.toFormation corridor hinterior offset prefixColor
      (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
        corridor hinterior offset cellColoring)
  let extra := pointwiseSelectedSourceLocalLayerSerialTrackedLocalGraphAt
    web.toFormation corridor hinterior offset spliced pair
  let oldVertex := fun slot : Fin current.card =>
    ((carrierCoordinate current).symm slot).1
  let newVertex :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt web
      corridor hinterior offset hnext
  have hcoordinate : forall old,
      newVertex (state.currentCoordinate old) = oldVertex old := by
    intro old
    exact
      pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt_currentEdge
        web corridor hinterior offset hnext hcell prefixColor hprefix old
  have hnewInjective : Function.Injective newVertex :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt_injective
      web corridor hinterior offset hnext
  have hsupport : extra.support ⊆ Set.range oldVertex :=
    pointwiseSelectedSourceLocalLayerSerialTrackedLocalGraphAt_support_subset_range
      web.toFormation corridor hinterior offset spliced pair
  have hadjacency : forall oldLeft oldRight,
      sourceLocalLayerSerialRootedTrackedLocalAdjacency
          state.toSourceLocalLayerSerialRootedCumulativeState factor hcount pair
          oldLeft oldRight = true ↔
        extra.Adj (oldVertex oldLeft) (oldVertex oldRight) := by
    intro oldLeft oldRight
    change Fin current.card at oldLeft oldRight
    have hnative :=
      pointwiseSelectedSourceLocalLayerSerialPhysicalTrackedLocalAdjacencyAt_eq
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring hcount pair
    have hnativeAt := congrFun (congrFun hnative oldLeft) oldRight
    rw [hnativeAt]
    simpa [extra, oldVertex, current, spliced] using
      pointwiseSelectedSourceLocalLayerSerialTrackedLocalAdjacencyAt_exact
        web corridor hinterior offset hcell spliced pair oldLeft oldRight
  exact liftInterfaceAdjacency_eq_true_iff extra oldVertex newVertex
    state.currentCoordinate hcoordinate hnewInjective hsupport
    (sourceLocalLayerSerialRootedTrackedLocalAdjacency
      state.toSourceLocalLayerSerialRootedCumulativeState factor hcount pair)
    hadjacency left right

/-- The literal Cell/seam graph is supported on the complete interaction
carrier, hence on the range of its canonical coordinate map. -/
theorem
    pointwiseSelectedSourceLocalLayerSerialTrackedLocalGraphAt_support_subset_interaction_range
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color) (pair : TrackedColorPair) :
    let edgeAt :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt web
        corridor hinterior offset hnext
    (pointwiseSelectedSourceLocalLayerSerialTrackedLocalGraphAt web.toFormation
      corridor hinterior offset color pair).support ⊆ Set.range edgeAt := by
  dsimp only
  intro edge hedge
  let current :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
      web.toFormation corridor hinterior offset
  let interaction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web corridor hinterior offset hnext
  have hcurrent : edge ∈ current :=
    pointwiseSelectedSourceLocalLayerSerialTrackedLocalGraphAt_support_subset_carrier
      web.toFormation corridor hinterior offset color pair hedge
  have hinteraction : edge ∈ interaction :=
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_subset_interaction
      web corridor hinterior offset hnext hcurrent
  refine ⟨carrierCoordinate interaction ⟨edge, hinteraction⟩, ?_⟩
  simp [interaction,
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt]

/-- At a compatible literal Cell, every row of the graph-free enlarged update
is the exact selected pre-rebase row on the complete interaction carrier. -/
theorem pointwiseSelectedSourceLocalLayerSerialRootedInteractionPreRebaseStateAt_code_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card <= 6)
    (prefixColor : G.edgeSet -> Color)
    (hprefix : forall step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt
        web.toFormation corridor hinterior offset step) ≠ 0)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset)
    (hcompatible :
      PointwiseSelectedSourceLocalLayerSerialTerminalCellColorsCompatibleAt
        web.toFormation corridor hinterior offset prefixColor
          (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
            corridor hinterior offset cellColoring))
    (hcount :
      (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
        ).trackedExterior.vertexCount =
      (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring).2.2.trackedGeometry.vertexCount)
    (pair : TrackedColorPair) :
    (sourceLocalLayerSerialRootedInteractionPreRebaseState
      (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web corridor hinterior offset hnext hcell prefixColor hprefix)
      (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring).2.2 hcount).code pair =
      (pointwiseSelectedSourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
        web corridor hinterior offset hnext hcell
          (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
            web.toFormation corridor hinterior offset prefixColor
            (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
              corridor hinterior offset cellColoring))).code pair := by
  classical
  let interaction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseTrackedInteractionCarrierAt
      web corridor hinterior offset hnext
  let edgeAt :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformTrackedEdgeAt web
      corridor hinterior offset hnext
  let cellColor := pointwiseSelectedSourceLocalLayerCellLiteralColorAt
    web.toFormation corridor hinterior offset cellColoring
  let spliced := pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
    web.toFormation corridor hinterior offset prefixColor cellColor
  let prefixGraph := regionalTrackedEdgeGraph web.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
      web.toFormation corridor hinterior offset)
    spliced (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  let localGraph := pointwiseSelectedSourceLocalLayerSerialTrackedLocalGraphAt
    web.toFormation corridor hinterior offset spliced pair
  let adjacency : Fin interaction.card -> Fin interaction.card -> Bool :=
    sourceLocalLayerSerialRootedInteractionLocalAdjacency
      (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt web
        corridor hinterior offset hnext hcell prefixColor hprefix)
      (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt web
        corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring).2.2 hcount pair
  have hprefixGraph : prefixGraph = regionalTrackedEdgeGraph web.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
        web.toFormation corridor hinterior offset)
      prefixColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 :=
    pointwiseSelectedRegionalTrackedEdgeGraph_spliced_eq_prefix web.toFormation
      corridor hinterior offset prefixColor cellColor hcompatible
        (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
  change addInterfaceAdjacency
      (exactInterfaceExteriorCode
        (regionalTrackedEdgeGraph web.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
            web.toFormation corridor hinterior offset)
          prefixColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2)
        edgeAt)
      adjacency =
    exactInterfaceExteriorCode
      (pointwiseSelectedPreRebaseTrackedGraphForColorAt web.toFormation corridor
        hinterior offset spliced pair) edgeAt
  rw [pointwiseSelectedPreRebaseTrackedGraphForColorAt,
    pointwiseSelectedSourceLocalLayerSerialPreRebaseTrackedGraph_eq_three_factor
      web.toFormation corridor hinterior offset spliced
        (trackedColorPairColors pair).1 (trackedColorPairColors pair).2,
    sup_assoc, ← hprefixGraph]
  apply addInterfaceAdjacency_exact_code_eq
  · exact
      pointwiseSelectedSourceLocalLayerSerialTrackedLocalGraphAt_support_subset_interaction_range
        web corridor hinterior offset hnext spliced pair
  · intro left right
    exact
      pointwiseSelectedSourceLocalLayerSerialRootedInteractionLocalAdjacencyAt_eq_true_iff
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring hcount pair left right

/-- The guarded forty-nine-coordinate update succeeds on every compatible
literal Cell and returns exactly the canonical selected interaction state. -/
theorem pointwiseSelectedSourceLocalLayerSerialRootedInteractionPreRebaseState?_at
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card <= 6)
    (prefixColor : G.edgeSet -> Color)
    (hprefix : forall step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt
        web.toFormation corridor hinterior offset step) ≠ 0)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset)
    (hcompatible :
      PointwiseSelectedSourceLocalLayerSerialTerminalCellColorsCompatibleAt
        web.toFormation corridor hinterior offset prefixColor
          (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
            corridor hinterior offset cellColoring)) :
    let state :=
      pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt web
        corridor hinterior offset hnext hcell prefixColor hprefix
    let factor :=
      (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt web
        corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring).2.2
    sourceLocalLayerSerialRootedInteractionPreRebaseState? state factor =
      some
        (pointwiseSelectedSourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
          web corridor hinterior offset hnext hcell
            (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
              web.toFormation corridor hinterior offset prefixColor
              (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
                corridor hinterior offset cellColoring))) := by
  classical
  let state :=
    pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt web
      corridor hinterior offset hnext hcell prefixColor hprefix
  let factor :=
    (pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt web
      corridor hinterior offset hnext hcell prefixColor hprefix cellColoring).2.2
  let expected :=
    pointwiseSelectedSourceLocalLayerSerialTrackedInteractionPreRebaseStateForColorAt
      web corridor hinterior offset hnext hcell
        (pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt web.toFormation
          corridor hinterior offset prefixColor
          (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
            corridor hinterior offset cellColoring))
  change sourceLocalLayerSerialRootedInteractionPreRebaseState? state factor =
    some expected
  unfold sourceLocalLayerSerialRootedInteractionPreRebaseState?
  split <;> rename_i hcount
  · congr 1
    unfold sourceLocalLayerSerialRootedInteractionPreRebaseState
    congr 1
    funext pair
    exact
      pointwiseSelectedSourceLocalLayerSerialRootedInteractionPreRebaseStateAt_code_eq
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring hcompatible hcount pair
  · exfalso
    apply hcount
    rfl

end

end GoertzelV24ClosedWebPointwiseSelectedTrackedPreRebaseExact

end Mettapedia.GraphTheory.FourColor
