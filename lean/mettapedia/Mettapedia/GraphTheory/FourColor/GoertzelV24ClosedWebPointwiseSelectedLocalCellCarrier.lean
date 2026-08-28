import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedSerialPrefixRegion
import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualPathTransversalFaceRetention
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebFiniteCutRadialEscape
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFourEdgeConnectedSides

/-!
# Finite carrier of a pointwise-selected literal Cell

The selected four-edge Cell wall has two connected primal sides without the
historical global shared-edge uniqueness receipt.  Its removed side avoids
both named annular caps, so it is locally cubic.  Consequently it is either
cyclic or has exactly two vertices and at most six incident regional edges.

This file is independent of minimality.  Eliminating the cyclic alternative
in the two-cap source laboratory is a separate consumer theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebComponentCensus
open GoertzelV24ClosedWebHoleBoundaryOrder
open GoertzelV24ClosedWebInnerTouching
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebTotalClosure
open GoertzelV24CubicFourEdgeConnectedSides
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SelectedDualPathTransversal
open GoertzelV24SelectedDualPathTransversal.SeparatedAlignedSelectedDualTransversals
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedLocalCellCarrierEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance pointwiseSelectedLocalCellCarrierLocallyFinite :
    G.LocallyFinite :=
  fun vertex =>
    @Subtype.fintype V (Membership.mem (G.neighborSet vertex))
      (inferInstance : DecidablePred (Membership.mem (G.neighborSet vertex)))
      inferInstance

namespace Formation.LocalLayerPair

/-- The literal Cell is the selected-deletion side opposite the retained
outer component. -/
noncomputable def pointwiseSelectedLocalLayerCellVertexSide
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext)
    (boundary : SourceSelectedBoundaryData
      formation.annular.cellulation.rotation
      (layers.pointwiseSelectedLocalLayerPair hinterior)) : Finset V :=
  ((layers.pointwiseSelectedLocalLayerPair hinterior).componentSide
    boundary.component)ᶜ

/-- Every outer-cap dart lies on the retained selected-deletion component. -/
theorem pointwiseSelectedLocalLayerPair_outerHole_vertex_mem_componentSide
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext)
    (boundary : SourceSelectedBoundaryData
      formation.annular.cellulation.rotation
      (layers.pointwiseSelectedLocalLayerPair hinterior))
    (dart : G.Dart)
    (hdart : dartOrbitFace formation.annular.RS dart =
      formation.annular.cellulation.outerHole) :
    formation.annular.RS.vertOf dart ∈
      (layers.pointwiseSelectedLocalLayerPair hinterior).componentSide
        boundary.component := by
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  apply boundary.face_vertex_mem_componentSide_of_root_and_boundary_avoids_primalCut
    formation.annular.cellulation.rotation pair formation.annular.RS.outer dart
  · exact (pair.mem_componentSide_iff boundary.component _).1
      boundary.outer_kept
  · intro edge hedge hvalue
    rcases (mem_edgeFinsetValueSet_iff
      (pair.primalCutEdges formation.annular.cellulation.rotation) edge.1).1
        hvalue with ⟨other, hother, hotherValue⟩
    have hedgeCut : edge ∈
        pair.primalCutEdges formation.annular.cellulation.rotation := by
      simpa [Subtype.ext hotherValue] using hother
    have hedgeOuter : edge ∈ orbitFaceBoundary formation.annular.RS
        formation.annular.cellulation.outerHole := by
      rw [formation.annular.outer_dart_on_outerHole] at hedge
      exact hedge
    exact (Finset.disjoint_left.mp
      (layers.pointwiseSelectedLocalLayerPair_primalCutEdges_disjoint_outerHoleBoundary
        hinterior) hedgeCut hedgeOuter)
  · exact hdart.trans formation.annular.outer_dart_on_outerHole.symm

/-- A selected four-edge Cell wall misses an actual radial path.  The path
transports retention from the outer cap to every dart of the inner cap. -/
theorem pointwiseSelectedLocalLayerPair_innerHole_vertex_mem_componentSide
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (layers : Formation.LocalLayerPair web.toFormation corridor leftInterior hnext)
    (boundary : SourceSelectedBoundaryData
      web.annular.cellulation.rotation
      (layers.pointwiseSelectedLocalLayerPair hinterior))
    (dart : G.Dart)
    (hdart : dartOrbitFace web.annular.RS dart =
      web.annular.cellulation.innerHole) :
    web.annular.RS.vertOf dart ∈
      (layers.pointwiseSelectedLocalLayerPair hinterior).componentSide
        boundary.component := by
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let rotationData := web.annular.cellulation.rotation
  have hcard : (pair.primalCutEdges rotationData).card < 5 := by
    have hexact : (pair.primalCutEdges rotationData).card = 4 := by
      change pair.crossingSupport.card = 4
      rw [pair.card_crossingSupport
        (orbitFace_incidence_le_two web.annular.RS)]
      norm_num [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
        Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
        Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
        Formation.LocalLayerPair.firstLayer,
        Formation.LocalLayerPair.secondLayer,
        Formation.LocalLayerPair.firstWalk,
        Formation.LocalLayerPair.secondWalk]
    omega
  obtain ⟨endpoint, havoids⟩ :=
    Instance.LocalLayerFormation.exists_radialPathOfInnerEnd_avoiding_finiteCut
      (web := web) (pair.primalCutEdges rotationData) hcard
  let hinnerTouching : EveryColorPairComponentInnerTouching data coloring :=
    everyColorPairComponentInnerTouching_of_totallyClosed
      data web.boundary_wellFormed web.connected coloring web.tait
        web.totallyClosed
  let radial := Instance.LocalLayerFormation.radialPathOfInnerEnd
    data web.boundary_wellFormed coloring web.tait hinnerTouching endpoint
  let source : G.Dart :=
    outerBoundaryDart data web.boundary_wellFormed radial.outer
  let root : G.Dart :=
    innerBoundaryDart data web.boundary_wellFormed radial.inner
  let bridge : G.Walk source.fst root.fst :=
    (ambientRadialPath radial).reverse.copy
      (by simpa [source] using radial.finish_eq_outerStub)
      (by simpa [root] using radial.start_eq_innerStub)
  have hsourceFace : dartOrbitFace web.annular.RS source =
      web.annular.cellulation.outerHole := by
    simpa [source] using outerBoundaryDart_on_outerHole
      web.annular web.boundary_wellFormed radial.outer
  have hrootFace : dartOrbitFace web.annular.RS root =
      web.annular.cellulation.innerHole := by
    simpa [root] using innerBoundaryDart_on_innerHole
      web.annular web.boundary_wellFormed radial.inner
  have hsourceSide : source.fst ∈ pair.componentSide boundary.component := by
    exact layers.pointwiseSelectedLocalLayerPair_outerHole_vertex_mem_componentSide
      hinterior boundary source hsourceFace
  have hsource : source.fst ∈ boundary.component.supp :=
    (pair.mem_componentSide_iff boundary.component source.fst).1 hsourceSide
  have hradialAvoid : ∀ edge : G.edgeSet,
      edge.1 ∈ (ambientRadialPath radial).edges →
        edge.1 ∉ edgeFinsetValueSet (pair.primalCutEdges rotationData) := by
    intro edge hedge hvalue
    rcases (mem_edgeFinsetValueSet_iff
      (pair.primalCutEdges rotationData) edge.1).1 hvalue with
      ⟨other, hother, hvalueEq⟩
    apply havoids other
    rw [hvalueEq]
    exact hedge
    exact hother
  apply boundary.face_vertex_mem_componentSide_of_bridge_and_boundary_avoids_primalCut
    rotationData pair source root dart bridge hsource
  · intro edge hedge
    apply hradialAvoid edge
    have hedgeReverse : (edge : Sym2 V) ∈
        (ambientRadialPath radial).edges.reverse := by
      simpa only [bridge, SimpleGraph.Walk.edges_copy,
        SimpleGraph.Walk.edges_reverse] using hedge
    exact List.mem_reverse.mp hedgeReverse
  · intro edge hedge hvalue
    rcases (mem_edgeFinsetValueSet_iff
      (pair.primalCutEdges rotationData) edge.1).1 hvalue with
      ⟨other, hother, hotherValue⟩
    have hedgeCut : edge ∈ pair.primalCutEdges rotationData := by
      simpa [Subtype.ext hotherValue] using hother
    have hedgeInner : edge ∈ orbitFaceBoundary web.annular.RS
        web.annular.cellulation.innerHole := by
      rw [hrootFace] at hedge
      exact hedge
    exact (Finset.disjoint_left.mp
      (layers.pointwiseSelectedLocalLayerPair_primalCutEdges_disjoint_innerHoleBoundary
        hinterior) hedgeCut hedgeInner)
  · exact hdart.trans hrootFace.symm

/-- The selected Cell side opposite the retained component is connected. -/
theorem pointwiseSelectedLocalLayerCellVertexSide_connected
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext)
    (boundary : SourceSelectedBoundaryData
      formation.annular.cellulation.rotation
      (layers.pointwiseSelectedLocalLayerPair hinterior)) :
    (G.induce (fun vertex => vertex ∈
      layers.pointwiseSelectedLocalLayerCellVertexSide
        hinterior boundary)).Connected := by
  have hconnected :=
    layers.pointwiseSelectedLocalLayerPair_complement_connected
      hinterior boundary
  have hside : (fun vertex => vertex ∈
      layers.pointwiseSelectedLocalLayerCellVertexSide hinterior boundary) =
      (fun vertex => vertex ∉ boundary.component.supp) := by
    funext vertex
    simp [pointwiseSelectedLocalLayerCellVertexSide]
  rw [hside]
  exact hconnected

/-- Both named caps lie on the retained side, so every selected Cell vertex
has ambient graph degree three. -/
theorem pointwiseSelectedLocalLayerCellVertexSide_degree_eq_three
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (layers : Formation.LocalLayerPair web.toFormation corridor leftInterior hnext)
    (boundary : SourceSelectedBoundaryData
      web.annular.cellulation.rotation
      (layers.pointwiseSelectedLocalLayerPair hinterior))
    (vertex : V)
    (hvertex : vertex ∈
      layers.pointwiseSelectedLocalLayerCellVertexSide hinterior boundary) :
    G.degree vertex = 3 := by
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  have hnotKept : vertex ∉ pair.componentSide boundary.component := by
    simpa [pointwiseSelectedLocalLayerCellVertexSide, pair] using hvertex
  have hnotInner : ∀ inner, vertex ≠ data.innerStub inner := by
    intro inner heq
    subst vertex
    apply hnotKept
    exact layers.pointwiseSelectedLocalLayerPair_innerHole_vertex_mem_componentSide
      hinterior boundary
      (innerBoundaryDart data web.boundary_wellFormed inner)
      (innerBoundaryDart_on_innerHole web.annular
        web.boundary_wellFormed inner)
  have hnotOuter : ∀ outer, vertex ≠ data.outerStub outer := by
    intro outer heq
    subst vertex
    apply hnotKept
    exact layers.pointwiseSelectedLocalLayerPair_outerHole_vertex_mem_componentSide
      hinterior boundary
      (outerBoundaryDart data web.boundary_wellFormed outer)
      (outerBoundaryDart_on_outerHole web.annular
        web.boundary_wellFormed outer)
  have hcubic := web.boundary_wellFormed.cubic_elsewhere vertex
    hnotInner hnotOuter
  exact (GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree
    (G := G) vertex).symm.trans hcubic

/-- The selected Cell side has exactly the four literal crossing edges. -/
theorem pointwiseSelectedLocalLayerCellVertexSide_crossingEdgeFinset_card_eq_four
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (layers : LocalLayerPair formation corridor leftInterior hnext)
    (boundary : SourceSelectedBoundaryData
      formation.annular.cellulation.rotation
      (layers.pointwiseSelectedLocalLayerPair hinterior)) :
    (crossingEdgeFinset G (fun vertex => vertex ∈
      layers.pointwiseSelectedLocalLayerCellVertexSide
        hinterior boundary)).card = 4 := by
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let rotationData := formation.annular.cellulation.rotation
  have hretained : crossingEdgeFinset G
      (fun vertex => vertex ∈ pair.componentSide boundary.component) =
      pair.primalCutEdges rotationData := by
    calc
      crossingEdgeFinset G
          (fun vertex => vertex ∈ pair.componentSide boundary.component) =
          componentCrossingEdges (pair.primalCutEdges rotationData)
            boundary.component := by
        ext edge
        rw [mem_crossingEdgeFinset_iff,
          mem_componentCrossingEdges_iff]
        simp only [pair.mem_componentSide_iff]
      _ = pair.primalCutEdges rotationData := boundary.component_boundary
  have hcompl := crossingEdgeFinset_compl
    (G := G) (fun vertex => vertex ∈ pair.componentSide boundary.component)
  calc
    (crossingEdgeFinset G (fun vertex => vertex ∈
        layers.pointwiseSelectedLocalLayerCellVertexSide
          hinterior boundary)).card =
        (crossingEdgeFinset G
          (fun vertex => vertex ∉ pair.componentSide boundary.component)).card := by
      congr 1
      ext edge
      rw [mem_crossingEdgeFinset_iff, mem_crossingEdgeFinset_iff]
      simp [pointwiseSelectedLocalLayerCellVertexSide, pair]
    _ = (crossingEdgeFinset G
          (fun vertex => vertex ∈ pair.componentSide boundary.component)).card := by
      rw [hcompl]
    _ = (pair.primalCutEdges rotationData).card := by rw [hretained]
    _ = 4 := by
      change pair.crossingSupport.card = 4
      rw [pair.card_crossingSupport
        (orbitFace_incidence_le_two formation.annular.RS)]
      norm_num [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
        Formation.LocalLayerPair.pointwiseSelectedFirstLayer,
        Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
        Formation.LocalLayerPair.firstLayer,
        Formation.LocalLayerPair.secondLayer,
        Formation.LocalLayerPair.firstWalk,
        Formation.LocalLayerPair.secondWalk]

/-- A selected Cell side is cyclic or consists of exactly two vertices. -/
theorem pointwiseSelectedLocalLayerCellVertexSide_card_eq_two_or_hasCycleOnSide
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (layers : Formation.LocalLayerPair web.toFormation corridor leftInterior hnext)
    (boundary : SourceSelectedBoundaryData
      web.annular.cellulation.rotation
      (layers.pointwiseSelectedLocalLayerPair hinterior)) :
    HasCycleOnSide G (fun vertex => vertex ∈
      layers.pointwiseSelectedLocalLayerCellVertexSide hinterior boundary) ∨
      (layers.pointwiseSelectedLocalLayerCellVertexSide
        hinterior boundary).card = 2 := by
  let side := layers.pointwiseSelectedLocalLayerCellVertexSide hinterior boundary
  have hnonempty : ∃ vertex, vertex ∈ side := by
    refine ⟨boundary.removed, ?_⟩
    simpa [side, pointwiseSelectedLocalLayerCellVertexSide] using
      boundary.removed_not_kept
  have hconnected : (G.induce fun vertex => vertex ∈ side).Connected := by
    simpa [side] using
      layers.pointwiseSelectedLocalLayerCellVertexSide_connected
        hinterior boundary
  have hdegree : ∀ vertex, vertex ∈ side → G.degree vertex = 3 := by
    intro vertex hvertex
    exact layers.pointwiseSelectedLocalLayerCellVertexSide_degree_eq_three
      hinterior boundary vertex hvertex
  have hboundary : (crossingEdgeFinset G
      (fun vertex => vertex ∈ side)).card = 4 := by
    simpa [side] using
      layers.pointwiseSelectedLocalLayerCellVertexSide_crossingEdgeFinset_card_eq_four
        hinterior boundary
  rcases hasCycleOnSide_or_card_eq_two_of_local_cubic_of_connected_of_boundary_card_eq_four
      (fun vertex => vertex ∈ side) hdegree hnonempty hconnected hboundary with
      hcycle | hcard
  · exact .inl hcycle
  · right
    simpa [side, Nat.card_eq_fintype_card] using hcard

/-- The selected source Cell is cyclic or has a graph-independent six-edge
regional carrier. -/
theorem pointwiseSelectedLocalLayerCellRegion_card_le_six_or_hasCycleOnSide
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (layers : Formation.LocalLayerPair web.toFormation corridor leftInterior hnext)
    (boundary : SourceSelectedBoundaryData
      web.annular.cellulation.rotation
      (layers.pointwiseSelectedLocalLayerPair hinterior)) :
    HasCycleOnSide G (fun vertex => vertex ∈
      layers.pointwiseSelectedLocalLayerCellVertexSide hinterior boundary) ∨
      (vertexSetRegionEdges web.annular.RS
        (layers.pointwiseSelectedLocalLayerCellVertexSide
          hinterior boundary)).card ≤ 6 := by
  let side := layers.pointwiseSelectedLocalLayerCellVertexSide hinterior boundary
  rcases layers.pointwiseSelectedLocalLayerCellVertexSide_card_eq_two_or_hasCycleOnSide
      hinterior boundary with hcycle | hcard
  · exact .inl hcycle
  · right
    have hsideCard : side.card = 2 := by
      simpa [side] using hcard
    have hlocalIncident : ∀ vertex ∈ side,
        (web.annular.RS.incidentEdges vertex).card = 3 := by
      intro vertex hvertex
      have hincidentEq : web.annular.RS.incidentEdges vertex =
          incidentEdgeFinset G vertex := by
        ext edge
        rw [GoertzelV24OrbitFaceCycleSpace.mem_toRotationSystem_incidentEdges_iff]
        simp [incidentEdgeFinset]
      rw [hincidentEq]
      rw [GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree]
      exact layers.pointwiseSelectedLocalLayerCellVertexSide_degree_eq_three
        hinterior boundary vertex hvertex
    have hle := vertexSetRegionEdges_card_le_three_mul_of_local
      web.annular.RS side hlocalIncident
    change (vertexSetRegionEdges web.annular.RS side).card ≤ 6
    omega

end Formation.LocalLayerPair

namespace Formation

/-- Canonical selected Cell vertex side at one serial offset. -/
noncomputable def pointwiseSelectedSourceLocalLayerCellVertexSideAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) : Finset V :=
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let boundary := pointwiseSelectedSourceLocalLayerBoundaryAt formation corridor
    hinterior offset
  layers.pointwiseSelectedLocalLayerCellVertexSide hinterior boundary

/-- The Count region used for the selected Cell is exactly the regional edge
carrier induced by its canonical removed-side vertex set. -/
theorem pointwiseSelectedSourceLocalLayerCellRegionAt_eq_vertexSetRegionEdges
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset =
      vertexSetRegionEdges formation.annular.RS
        (pointwiseSelectedSourceLocalLayerCellVertexSideAt formation corridor
          hinterior offset) := by
  rfl

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
