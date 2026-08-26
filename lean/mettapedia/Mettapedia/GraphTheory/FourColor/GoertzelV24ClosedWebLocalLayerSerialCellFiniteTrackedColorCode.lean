import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedCarrierBoolGraphFamilyCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedFiniteClosure

/-!
# Recompute tracked Cell factors from finite colours and geometry

A stored tracked seam graph is not a prefix-independent Cell letter: its
edges depend on the colours carried by both the cumulative prefix and the new
Cell.  This file exposes the exact finite dependence instead.

The local geometric datum is one uncoloured edge-adjacency graph on the common
twenty-one-slot transition carrier.  The predecessor and Cell contribute the
partial colour tables proved exact in the preceding module.  From these three
finite objects we reconstruct the tracked Cell graph and the old/new residual
seam for every tracked colour pair.

The source-specific reflection theorems below compare the reconstructed graphs
with the literal graph factors.  Thus the finite alphabet need not store a
seam already specialized to one cumulative prefix.  Boundary rebasing and
the complete five-field transition remain separate subsequent steps.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedColorCode

open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24TerminalProfileSeamResidual
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section


local instance openedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The uncoloured common-carrier geometry of one literal source Cell. -/
noncomputable def sourceLocalLayerSerialTrackedGeometryCodeAt
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
    (offset : Fin (blockLength - 3)) :
    BoundedCarrierGraphFamilyCode 21 5 Unit :=
  boundedCarrierGraphFamilyCode
    (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
      web corridor hunique offset) 21 5
    (sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      graphData minimal caps coloring web corridor hunique offset)
    (sourceLocalLayerSerialTrackedTransitionPointAt graphData caps coloring web
      corridor hunique offset)
    (fun _ => web.annular.RS.edgeAdjacencyGraph)

/-- Embed a live geometry coordinate into the stable twenty-one-slot ABI. -/
def SourceLocalLayerSerialTrackedGeometryStableSlot
    (geometry : BoundedCarrierGraphFamilyCode 21 5 Unit)
    (coordinate : Fin geometry.vertexCount.val) : Fin 21 :=
  Fin.castLE (Nat.le_of_lt_succ geometry.vertexCount.isLt) coordinate

/-- The geometric code preserves literal edge adjacency on every represented
transition-carrier edge. -/
theorem sourceLocalLayerSerialTrackedGeometryCodeAt_adj_iff
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
    (first second : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    ((sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
      coloring web corridor hunique offset).graph ()).Adj
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      web.annular.RS.edgeAdjacencyGraph.Adj first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_adj_iff _ 21 5
    (sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      graphData minimal caps coloring web corridor hunique offset)
    (sourceLocalLayerSerialTrackedTransitionPointAt graphData caps coloring web
      corridor hunique offset)
    (fun _ => web.annular.RS.edgeAdjacencyGraph) () first second

/-- The live-to-stable embedding of the geometry code is the same embedding
used by the canonical literal transition carrier. -/
@[simp]
theorem sourceLocalLayerSerialTrackedGeometryStableSlot_coordinate
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
    (edge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    SourceLocalLayerSerialTrackedGeometryStableSlot
        (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
          coloring web corridor hunique offset)
        (carrierCoordinate _ edge) =
      sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
        coloring web corridor hunique offset edge := by
  rfl

/-- A partial colour table says that a stable slot is present and carries one
of the selected tracked colours. -/
def SourceLocalLayerSerialCarrierHasTrackedColor
    (code : SourceLocalLayerSerialCarrierColorCode)
    (pair : TrackedColorPair) (slot : Fin 21) : Prop :=
  ∃ color,
    code slot = some color ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 color

/-- Regional membership and the literal colour are recovered exactly at a
represented stable slot. -/
theorem sourceLocalLayerSerialCarrierHasTrackedColor_codeAt_slot_iff
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
    (region : Finset
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet -> Color)
    (pair : TrackedColorPair)
    (edge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    SourceLocalLayerSerialCarrierHasTrackedColor
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset region color)
        pair
        (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
          coloring web corridor hunique offset edge) ↔
      edge.1 ∈ region ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 (color edge.1) := by
  unfold SourceLocalLayerSerialCarrierHasTrackedColor
  rw [sourceLocalLayerSerialCarrierColorCodeAt_slot]
  by_cases hedge : edge.1 ∈ region
  · simp [hedge]
  · simp [hedge]

/-- A represented stable slot is active in the partial table exactly when its
literal edge belongs to the selected region. -/
theorem sourceLocalLayerSerialCarrierColorCodeAt_exists_eq_some_slot_iff
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
    (region : Finset
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet -> Color)
    (edge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    (∃ value,
      sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset region color
          (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
            coloring web corridor hunique offset edge) = some value) ↔
      edge.1 ∈ region := by
  rw [sourceLocalLayerSerialCarrierColorCodeAt_slot]
  by_cases hedge : edge.1 ∈ region <;> simp [hedge]

/-- Dually, `none` records exact non-membership rather than an isolated
reachability convention. -/
theorem sourceLocalLayerSerialCarrierColorCodeAt_eq_none_slot_iff
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
    (region : Finset
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet -> Color)
    (edge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset region color
        (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
          coloring web corridor hunique offset edge) = none ↔
      edge.1 ∉ region := by
  rw [sourceLocalLayerSerialCarrierColorCodeAt_slot]
  by_cases hedge : edge.1 ∈ region <;> simp [hedge]

/-- Cell colours take precedence over prefix colours, exactly as in the
literal splice. -/
def SourceLocalLayerSerialFiniteSplicedColor
    (oldCode cellCode : SourceLocalLayerSerialCarrierColorCode) :
    SourceLocalLayerSerialCarrierColorCode :=
  fun slot =>
    match cellCode slot with
    | some color => some color
    | none => oldCode slot

/-- The finite splice is active exactly on the union and carries the literal
spliced colour at every represented edge. -/
theorem sourceLocalLayerSerialFiniteSplicedColor_codeAt_slot
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet -> Color)
    (edge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    SourceLocalLayerSerialFiniteSplicedColor
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          coloring)
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor)
        (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
          coloring web corridor hunique offset edge) =
      if edge.1 ∈ sourceLocalLayerCellRegionAt corridor hunique offset then
        some (cellColor edge.1)
      else if edge.1 ∈
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset then
        some (coloring edge.1)
      else none := by
  unfold SourceLocalLayerSerialFiniteSplicedColor
  rw [sourceLocalLayerSerialCarrierColorCodeAt_slot,
    sourceLocalLayerSerialCarrierColorCodeAt_slot]
  by_cases hcell : edge.1 ∈
      sourceLocalLayerCellRegionAt corridor hunique offset
  · simp [hcell]
  · simp [hcell]

/-- Prefix-parametric form of the finite-splice coordinate equation.  The
ambient colouring continues to determine the literal carrier only. -/
theorem sourceLocalLayerSerialFiniteSplicedColorForColorAt_codeAt_slot
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
    (prefixColor cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet -> Color)
    (edge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    SourceLocalLayerSerialFiniteSplicedColor
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          prefixColor)
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor)
        (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
          coloring web corridor hunique offset edge) =
      if edge.1 ∈ sourceLocalLayerCellRegionAt corridor hunique offset then
        some (cellColor edge.1)
      else if edge.1 ∈
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset then
        some (prefixColor edge.1)
      else none := by
  unfold SourceLocalLayerSerialFiniteSplicedColor
  rw [sourceLocalLayerSerialCarrierColorCodeAt_slot,
    sourceLocalLayerSerialCarrierColorCodeAt_slot]
  by_cases hcell : edge.1 ∈
      sourceLocalLayerCellRegionAt corridor hunique offset
  · simp [hcell]
  · simp [hcell]

/-- The finite splice carries a tracked colour exactly when the literal edge
lies in the union and its spliced colour is tracked. -/
theorem sourceLocalLayerSerialCarrierHasTrackedColor_spliced_codeAt_slot_iff
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet -> Color)
    (pair : TrackedColorPair)
    (edge : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    SourceLocalLayerSerialCarrierHasTrackedColor
        (SourceLocalLayerSerialFiniteSplicedColor
          (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
            corridor hunique offset
            (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
            coloring)
          (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
            corridor hunique offset
            (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor))
        pair
        (sourceLocalLayerSerialTrackedTransitionSlotAt graphData minimal caps
          coloring web corridor hunique offset edge) ↔
      edge.1 ∈
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∪
            sourceLocalLayerCellRegionAt corridor hunique offset ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            coloring cellColor edge.1) := by
  unfold SourceLocalLayerSerialCarrierHasTrackedColor
  rw [sourceLocalLayerSerialFiniteSplicedColor_codeAt_slot]
  by_cases hcell : edge.1 ∈
      sourceLocalLayerCellRegionAt corridor hunique offset
  · simp [sourceLocalLayerSerialCellSplicedColorAt, hcell]
  · by_cases hold : edge.1 ∈
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset
    · simp [sourceLocalLayerSerialCellSplicedColorAt, hcell, hold]
    · simp [sourceLocalLayerSerialCellSplicedColorAt, hcell, hold]

/-- The Cell tracked graph reconstructed from finite geometry and the Cell's
partial colour table. -/
def SourceLocalLayerSerialFiniteCellTrackedGraph
    (geometry : BoundedCarrierGraphFamilyCode 21 5 Unit)
    (cellCode : SourceLocalLayerSerialCarrierColorCode)
    (pair : TrackedColorPair) : SimpleGraph (Fin geometry.vertexCount.val) where
  Adj first second :=
    (geometry.graph ()).Adj first second ∧
      SourceLocalLayerSerialCarrierHasTrackedColor cellCode pair
        (SourceLocalLayerSerialTrackedGeometryStableSlot geometry first) ∧
      SourceLocalLayerSerialCarrierHasTrackedColor cellCode pair
        (SourceLocalLayerSerialTrackedGeometryStableSlot geometry second)
  symm := ⟨by
    rintro first second ⟨hadj, hfirst, hsecond⟩
    exact ⟨hadj.symm, hsecond, hfirst⟩⟩
  loopless := ⟨by
    intro edge hedge
    exact (geometry.graph ()).loopless.irrefl edge hedge.1⟩

/-- On the canonical source carrier, the reconstructed Cell graph is exactly
the literal regional tracked graph. -/
theorem sourceLocalLayerSerialFiniteCellTrackedGraphAt_adj_iff
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet -> Color)
    (pair : TrackedColorPair)
    (first second : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    (SourceLocalLayerSerialFiniteCellTrackedGraph
      (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
        coloring web corridor hunique offset)
      (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset
        (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor)
      pair).Adj (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
        (regionalTrackedEdgeGraph web.annular.RS
          (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor
          (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Adj first.1 second.1 := by
  change
    ((sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
        coloring web corridor hunique offset).graph ()).Adj
        (carrierCoordinate _ first) (carrierCoordinate _ second) ∧
      SourceLocalLayerSerialCarrierHasTrackedColor
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor)
        pair
        (SourceLocalLayerSerialTrackedGeometryStableSlot
          (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
            coloring web corridor hunique offset) (carrierCoordinate _ first)) ∧
      SourceLocalLayerSerialCarrierHasTrackedColor
        (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
          corridor hunique offset
          (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor)
        pair
        (SourceLocalLayerSerialTrackedGeometryStableSlot
          (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
            coloring web corridor hunique offset) (carrierCoordinate _ second)) ↔ _
  rw [sourceLocalLayerSerialTrackedGeometryCodeAt_adj_iff,
    sourceLocalLayerSerialTrackedGeometryStableSlot_coordinate,
    sourceLocalLayerSerialTrackedGeometryStableSlot_coordinate,
    sourceLocalLayerSerialCarrierHasTrackedColor_codeAt_slot_iff,
    sourceLocalLayerSerialCarrierHasTrackedColor_codeAt_slot_iff]
  change
    web.annular.RS.edgeAdjacencyGraph.Adj first.1 second.1 ∧
      (first.1 ∈ sourceLocalLayerCellRegionAt corridor hunique offset ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 (cellColor first.1)) ∧
      (second.1 ∈ sourceLocalLayerCellRegionAt corridor hunique offset ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 (cellColor second.1)) ↔
      ((web.annular.RS.edgeAdjacencyGraph.Adj first.1 second.1 ∧
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2 (cellColor first.1) ∧
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2 (cellColor second.1)) ∧
        first.1 ∈ sourceLocalLayerCellRegionAt corridor hunique offset ∧
        second.1 ∈ sourceLocalLayerCellRegionAt corridor hunique offset)
  aesop

/-- The residual tracked seam reconstructed from the same geometry and the two
partial colour tables. -/
def SourceLocalLayerSerialFiniteTrackedSeamGraph
    (geometry : BoundedCarrierGraphFamilyCode 21 5 Unit)
    (oldCode cellCode : SourceLocalLayerSerialCarrierColorCode)
    (pair : TrackedColorPair) : SimpleGraph (Fin geometry.vertexCount.val) where
  Adj first second :=
    (geometry.graph ()).Adj first second ∧
      SourceLocalLayerSerialCarrierHasTrackedColor
        (SourceLocalLayerSerialFiniteSplicedColor oldCode cellCode) pair
        (SourceLocalLayerSerialTrackedGeometryStableSlot geometry first) ∧
      SourceLocalLayerSerialCarrierHasTrackedColor
        (SourceLocalLayerSerialFiniteSplicedColor oldCode cellCode) pair
        (SourceLocalLayerSerialTrackedGeometryStableSlot geometry second) ∧
      (((∃ color, oldCode
              (SourceLocalLayerSerialTrackedGeometryStableSlot geometry first) =
                some color) ∧
          cellCode
              (SourceLocalLayerSerialTrackedGeometryStableSlot geometry first) =
                none ∧
          (∃ color, cellCode
              (SourceLocalLayerSerialTrackedGeometryStableSlot geometry second) =
                some color) ∧
          oldCode
              (SourceLocalLayerSerialTrackedGeometryStableSlot geometry second) =
                none) ∨
        ((∃ color, cellCode
              (SourceLocalLayerSerialTrackedGeometryStableSlot geometry first) =
                some color) ∧
          oldCode
              (SourceLocalLayerSerialTrackedGeometryStableSlot geometry first) =
                none ∧
          (∃ color, oldCode
              (SourceLocalLayerSerialTrackedGeometryStableSlot geometry second) =
                some color) ∧
          cellCode
              (SourceLocalLayerSerialTrackedGeometryStableSlot geometry second) =
                none))
  symm := ⟨by
    rintro first second ⟨hadj, hfirst, hsecond, hcross⟩
    refine ⟨hadj.symm, hsecond, hfirst, ?_⟩
    rcases hcross with hcross | hcross
    · exact Or.inr
        ⟨hcross.2.2.1, hcross.2.2.2, hcross.1, hcross.2.1⟩
    · exact Or.inl
        ⟨hcross.2.2.1, hcross.2.2.2, hcross.1, hcross.2.1⟩⟩
  loopless := ⟨by
    intro edge hedge
    exact (geometry.graph ()).loopless.irrefl edge hedge.1⟩

/-- On the canonical source carrier, the reconstructed seam is exactly the
literal residual seam between the cumulative prefix and the Cell. -/
theorem sourceLocalLayerSerialFiniteTrackedSeamGraphAt_adj_iff
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet -> Color)
    (pair : TrackedColorPair)
    (first second : {edge // edge ∈
      sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset}) :
    (SourceLocalLayerSerialFiniteTrackedSeamGraph
      (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
        coloring web corridor hunique offset)
      (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        coloring)
      (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset
        (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor)
      pair).Adj (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
        (sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            coloring cellColor)
          (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Adj first.1 second.1 := by
  unfold SourceLocalLayerSerialFiniteTrackedSeamGraph
  simp only [sourceLocalLayerSerialTrackedGeometryStableSlot_coordinate]
  rw [sourceLocalLayerSerialTrackedGeometryCodeAt_adj_iff,
    sourceLocalLayerSerialCarrierHasTrackedColor_spliced_codeAt_slot_iff,
    sourceLocalLayerSerialCarrierHasTrackedColor_spliced_codeAt_slot_iff,
    sourceLocalLayerSerialCarrierColorCodeAt_exists_eq_some_slot_iff,
    sourceLocalLayerSerialCarrierColorCodeAt_eq_none_slot_iff,
    sourceLocalLayerSerialCarrierColorCodeAt_exists_eq_some_slot_iff,
    sourceLocalLayerSerialCarrierColorCodeAt_eq_none_slot_iff,
    sourceLocalLayerSerialCarrierColorCodeAt_exists_eq_some_slot_iff,
    sourceLocalLayerSerialCarrierColorCodeAt_eq_none_slot_iff,
    sourceLocalLayerSerialCarrierColorCodeAt_exists_eq_some_slot_iff,
    sourceLocalLayerSerialCarrierColorCodeAt_eq_none_slot_iff]
  unfold sourceLocalLayerSerialTerminalTrackedSeamAt
  rw [regionalTrackedSeamGraph_adj_iff]
  change
    web.annular.RS.edgeAdjacencyGraph.Adj first.1 second.1 ∧
      (first.1 ∈
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∪
            sourceLocalLayerCellRegionAt corridor hunique offset ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            coloring cellColor first.1)) ∧
      (second.1 ∈
          sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∪
            sourceLocalLayerCellRegionAt corridor hunique offset ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            coloring cellColor second.1)) ∧
      ((first.1 ∈
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∧
          first.1 ∉ sourceLocalLayerCellRegionAt corridor hunique offset ∧
          second.1 ∈ sourceLocalLayerCellRegionAt corridor hunique offset ∧
          second.1 ∉
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset) ∨
        (first.1 ∈ sourceLocalLayerCellRegionAt corridor hunique offset ∧
          first.1 ∉
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∧
          second.1 ∈
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∧
          second.1 ∉ sourceLocalLayerCellRegionAt corridor hunique offset)) ↔
      ((web.annular.RS.edgeAdjacencyGraph.Adj first.1 second.1 ∧
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              coloring cellColor first.1) ∧
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              coloring cellColor second.1)) ∧
        ((first.1 ∈
              sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∧
            first.1 ∉ sourceLocalLayerCellRegionAt corridor hunique offset ∧
            second.1 ∈ sourceLocalLayerCellRegionAt corridor hunique offset ∧
            second.1 ∉
              sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset) ∨
          (first.1 ∈ sourceLocalLayerCellRegionAt corridor hunique offset ∧
            first.1 ∉
              sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∧
            second.1 ∈
              sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset ∧
            second.1 ∉ sourceLocalLayerCellRegionAt corridor hunique offset)))
  aesop

/-- The complete color-parametric tracked transition code reconstructed from
prefix-independent geometry and the two finite colour tables. -/
def sourceLocalLayerSerialTrackedCodeOfFiniteColors
    (geometry : BoundedCarrierGraphFamilyCode 21 5 Unit)
    (oldCode cellCode : SourceLocalLayerSerialCarrierColorCode) :
    BoundedCarrierGraphFamilyCode 21 5 (TrackedColorPair × Bool) where
  vertexCount := geometry.vertexCount
  point := geometry.point
  graph factor :=
    if factor.2 then
      SourceLocalLayerSerialFiniteTrackedSeamGraph geometry oldCode cellCode
        factor.1
    else
      SourceLocalLayerSerialFiniteCellTrackedGraph geometry cellCode factor.1

/-- Its Boolean reflection is the executable tracked local factor consumed by
the finite closure engine. -/
def sourceLocalLayerSerialTrackedBoolCodeOfFiniteColors
    (geometry : BoundedCarrierGraphFamilyCode 21 5 Unit)
    (oldCode cellCode : SourceLocalLayerSerialCarrierColorCode) :
    BoundedCarrierBoolGraphFamilyCode 21 5 (TrackedColorPair × Bool) :=
  ofGraphFamilyCode
    (sourceLocalLayerSerialTrackedCodeOfFiniteColors geometry oldCode cellCode)

/-- For literal source data, every reconstructed tracked factor is the same
graph as the formerly stored prefix-specialized factor.  This is the exact
factorization which removes the prefix dependency from the Cell alphabet. -/
theorem sourceLocalLayerSerialTrackedCodeOfFiniteColorsAt_graph_eq
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet -> Color)
    (factor : TrackedColorPair × Bool) :
    (sourceLocalLayerSerialTrackedCodeOfFiniteColors
      (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
        coloring web corridor hunique offset)
      (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        coloring)
      (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset
        (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor)
      ).graph factor =
        (sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData minimal
          caps coloring web corridor hunique offset
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            coloring cellColor)).graph factor := by
  let carrier := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
    coloring web corridor hunique offset
  let coordinate := carrierCoordinate carrier
  apply SimpleGraph.ext
  funext left right
  apply propext
  let first := coordinate.symm left
  let second := coordinate.symm right
  have hleft : coordinate first = left := coordinate.apply_symm_apply left
  have hright : coordinate second = right := coordinate.apply_symm_apply right
  rw [← hleft, ← hright]
  rcases factor with ⟨pair, seam⟩
  cases seam
  · have hfinite := sourceLocalLayerSerialFiniteCellTrackedGraphAt_adj_iff
      graphData minimal caps coloring web corridor hunique offset cellColor pair
      first second
    have hstored := boundedCarrierGraphFamilyCode_adj_iff carrier 21 5
      (sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
        graphData minimal caps coloring web corridor hunique offset)
      (sourceLocalLayerSerialTrackedTransitionPointAt graphData caps coloring web
        corridor hunique offset)
      (fun factor : TrackedColorPair × Bool =>
        if factor.2 then
          sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              coloring cellColor)
            (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2
        else
          regionalTrackedEdgeGraph web.annular.RS
            (sourceLocalLayerCellRegionAt corridor hunique offset)
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              coloring cellColor)
            (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2)
      (pair, false) first second
    have hcellColor : ∀ edge,
        edge ∈ sourceLocalLayerCellRegionAt corridor hunique offset ->
          sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            coloring cellColor edge = cellColor edge := by
      intro edge hedge
      exact sourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem corridor
        hunique offset coloring cellColor hedge
    have hregional :
        regionalTrackedEdgeGraph web.annular.RS
            (sourceLocalLayerCellRegionAt corridor hunique offset)
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              coloring cellColor)
            (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2 =
          regionalTrackedEdgeGraph web.annular.RS
            (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor
            (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2 := by
      ext left right
      simp only [regionalTrackedEdgeGraph, RotationSystem.trackedEdgeGraph]
      constructor
      · rintro ⟨⟨hadj, hleftTracked, hrightTracked⟩, hleft, hright⟩
        exact ⟨⟨hadj, (hcellColor left hleft) ▸ hleftTracked,
          (hcellColor right hright) ▸ hrightTracked⟩, hleft, hright⟩
      · rintro ⟨⟨hadj, hleftTracked, hrightTracked⟩, hleft, hright⟩
        exact ⟨⟨hadj, (hcellColor left hleft).symm ▸ hleftTracked,
          (hcellColor right hright).symm ▸ hrightTracked⟩, hleft, hright⟩
    rw [hregional] at hstored
    exact hfinite.trans (by
      simpa [sourceLocalLayerSerialTrackedCodeOfFiniteColors,
        sourceLocalLayerSerialTrackedTransitionCodeForColorAt, carrier,
        coordinate] using hstored.symm)
  · have hfinite := sourceLocalLayerSerialFiniteTrackedSeamGraphAt_adj_iff
      graphData minimal caps coloring web corridor hunique offset cellColor pair
      first second
    have hstored := boundedCarrierGraphFamilyCode_adj_iff carrier 21 5
      (sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
        graphData minimal caps coloring web corridor hunique offset)
      (sourceLocalLayerSerialTrackedTransitionPointAt graphData caps coloring web
        corridor hunique offset)
      (fun factor : TrackedColorPair × Bool =>
        if factor.2 then
          sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              coloring cellColor)
            (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2
        else
          regionalTrackedEdgeGraph web.annular.RS
            (sourceLocalLayerCellRegionAt corridor hunique offset)
            (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
              coloring cellColor)
            (trackedColorPairColors factor.1).1
            (trackedColorPairColors factor.1).2)
      (pair, true) first second
    exact hfinite.trans (by
      simpa [sourceLocalLayerSerialTrackedCodeOfFiniteColors,
        sourceLocalLayerSerialTrackedTransitionCodeForColorAt, carrier,
        coordinate] using hstored.symm)

/-- Consequently the finite reconstruction preserves complete component
reachability in both the Cell and seam factors. -/
theorem sourceLocalLayerSerialTrackedCodeOfFiniteColorsAt_reachable_iff
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
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet -> Color)
    (factor : TrackedColorPair × Bool)
    (left right : Fin
      (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
        coloring web corridor hunique offset).vertexCount.val) :
    ((sourceLocalLayerSerialTrackedCodeOfFiniteColors
      (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
        coloring web corridor hunique offset)
      (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        coloring)
      (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset
        (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor)
      ).graph factor).Reachable left right ↔
        ((sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData minimal
          caps coloring web corridor hunique offset
          (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
            coloring cellColor)).graph factor).Reachable left right := by
  rw [sourceLocalLayerSerialTrackedCodeOfFiniteColorsAt_graph_eq]
  rfl

end

end GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedColorCode

end Mettapedia.GraphTheory.FourColor
