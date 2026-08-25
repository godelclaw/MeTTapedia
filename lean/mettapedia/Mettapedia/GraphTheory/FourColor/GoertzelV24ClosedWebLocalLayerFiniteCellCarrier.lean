import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerRadialEscape
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFourEdgeConnectedSides

/-!
# The actual source-local Cell has a finite carrier unless it encloses a cycle

The opened annular source is not globally cubic: its ten named boundary stubs
have degree one.  The literal Cell side of a local layer avoids both named
holes, however, so every vertex on that side is locally cubic.  Its exact
four-edge boundary then gives a sharp dichotomy: either the Cell encloses a
primal cycle, or it consists of exactly two vertices and its full regional
edge carrier has size at most six.

This is the non-vacuous replacement for the earlier closed-cubic conditional
carrier bound.  It does not exclude the cyclic branch; that is the remaining
one-sided-cycle obligation at the source construction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebHoleBoundaryOrder
open GoertzelV24CubicFourEdgeConnectedSides
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24FramedLocalDualCycleSeparator
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerFiniteCellCarrierEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance closedWebLocalLayerFiniteCellCarrierLocallyFinite :
    G.LocallyFinite :=
  fun vertex =>
    @Subtype.fintype V (Membership.mem (G.neighborSet vertex))
      (inferInstance : DecidablePred (Membership.mem (G.neighborSet vertex)))
      inferInstance

namespace Instance

namespace LocalLayerPair

/-- A component behind the literal local Cell wall has a connected
complement once its computed boundary saturates that wall.  Local
two-sidedness of the loop support proves the same saturation for every other
deletion component, so no global face-two-sidedness premise is needed. -/
theorem cellSide_connected_of_component_boundary
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (component :
      (G.deleteEdges (localEdgeFinsetValueSet
        (layers.cutEdges hunique))).ConnectedComponent)
    (hboundary : localComponentCrossingEdges (layers.cutEdges hunique) component =
      layers.cutEdges hunique) :
    (G.induce (fun vertex => vertex ∉ component.supp)).Connected := by
  have hcutNonempty : (layers.cutEdges hunique).Nonempty := by
    apply Finset.card_pos.mp
    rw [layers.cutEdges_card_eq_four hunique]
    omega
  have hsaturationLocal : ∀ other :
      (G.deleteEdges (localEdgeFinsetValueSet
        (layers.cutEdges hunique))).ConnectedComponent,
      localComponentCrossingEdges (layers.cutEdges hunique) other =
        layers.cutEdges hunique := by
    intro other
    by_cases hother : other = component
    · simpa [hother] using hboundary
    · exact layers.componentCrossingEdges_eq_cutEdges_of_distinct
        hunique other component hother
  have hsaturation : ∀ other :
      (G.deleteEdges (edgeFinsetValueSet
        (layers.cutEdges hunique))).ConnectedComponent,
      GoertzelV24FiniteEdgeDeletion.componentCrossingEdges
          (layers.cutEdges hunique) other = layers.cutEdges hunique := by
    intro other
    have hlocal := hsaturationLocal other
    calc
      GoertzelV24FiniteEdgeDeletion.componentCrossingEdges
          (layers.cutEdges hunique) other =
          localComponentCrossingEdges (layers.cutEdges hunique) other := by
        ext edge
        simp only [GoertzelV24FiniteEdgeDeletion.mem_componentCrossingEdges_iff,
          mem_localComponentCrossingEdges_iff]
        rfl
      _ = layers.cutEdges hunique := hlocal
  exact induce_complement_connected_of_component_boundary_saturation
    (G := G) (removed := layers.cutEdges hunique) component hcutNonempty hsaturation

end LocalLayerPair

namespace LocalLayerFormation

/-- The literal Cell is the side opposite the retained deletion component
selected by the source-local boundary package. -/
noncomputable def sourceLocalLayerCellVertexSide
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) : Finset V :=
  Finset.univ.filter fun vertex => vertex ∉
    ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
      hunique).componentSide
      (sourceLocalLayerPairCrosscutBoundaryData corridor hunique
        leftInterior hnext).component

/-- The complement of the retained component is connected for the literal
local Cell wall.  The proof uses the already-established local two-sidedness
of faces on that wall, not the false global two-sidedness of the opened
annulus. -/
theorem sourceLocalLayerPair_cellSide_connected
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    (G.induce (fun vertex => vertex ∉
      ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique).componentSide
        (sourceLocalLayerPairCrosscutBoundaryData corridor hunique
          leftInterior hnext).component)).Connected := by
  let layers := sourceLocalLayerPair corridor hunique leftInterior hnext
  let pair := layers.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
    leftInterior hnext
  have hboundary : localComponentCrossingEdges (layers.cutEdges hunique)
      boundary.component = layers.cutEdges hunique := by
    calc
      localComponentCrossingEdges (layers.cutEdges hunique) boundary.component =
          GoertzelV24FiniteEdgeDeletion.componentCrossingEdges
            (pair.primalCutEdges web.annular.cellulation.rotation)
            boundary.component := by
        ext edge
        simp only [mem_localComponentCrossingEdges_iff,
          GoertzelV24FiniteEdgeDeletion.mem_componentCrossingEdges_iff]
        rfl
      _ = pair.primalCutEdges web.annular.cellulation.rotation :=
        boundary.component_boundary
      _ = layers.cutEdges hunique := by rfl
  have hconnected := layers.cellSide_connected_of_component_boundary
    hunique boundary.component hboundary
  have hsideEq :
      (fun vertex => vertex ∉ pair.componentSide boundary.component) =
        (fun vertex => vertex ∉ boundary.component.supp) := by
    funext vertex
    apply propext
    simp only [pair.mem_componentSide_iff]
  change (G.induce
    (fun vertex => vertex ∉ pair.componentSide boundary.component)).Connected
  rw [hsideEq]
  exact hconnected

/-- Both named hole interfaces lie on the retained side, so every vertex of
the literal Cell side has graph degree three. -/
theorem sourceLocalLayerCellVertexSide_degree_eq_three
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (vertex : V)
    (hvertex : vertex ∈ sourceLocalLayerCellVertexSide corridor hunique
      leftInterior hnext) :
    G.degree vertex = 3 := by
  let pair :=
    (sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
      hunique
  let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
    leftInterior hnext
  have hnotKept : vertex ∉ pair.componentSide boundary.component := by
    simpa [sourceLocalLayerCellVertexSide, pair, boundary] using hvertex
  have hnotInner : ∀ inner, vertex ≠ data.innerStub inner := by
    intro inner heq
    subst vertex
    apply hnotKept
    exact sourceLocalLayerPair_innerHole_vertex_mem_componentSide_of_radialEscape
      corridor hunique leftInterior hnext
        (innerBoundaryDart data web.boundary_wellFormed inner)
        (innerBoundaryDart_on_innerHole web.annular
          web.boundary_wellFormed inner)
  have hnotOuter : ∀ outer, vertex ≠ data.outerStub outer := by
    intro outer heq
    subst vertex
    apply hnotKept
    exact sourceLocalLayerPair_outerHole_vertex_mem_componentSide
      corridor hunique leftInterior hnext
        (outerBoundaryDart data web.boundary_wellFormed outer)
        (outerBoundaryDart_on_outerHole web.annular
          web.boundary_wellFormed outer)
  have hcubic := web.boundary_wellFormed.cubic_elsewhere vertex
    hnotInner hnotOuter
  exact (GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree
    (G := G) vertex).symm.trans hcubic

/-- The actual source-local Cell has exactly four outgoing graph edges. -/
theorem sourceLocalLayerCellVertexSide_crossingEdgeFinset_card_eq_four
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    (crossingEdgeFinset G (fun vertex => vertex ∈
      sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext)).card = 4 := by
  let layers := sourceLocalLayerPair corridor hunique leftInterior hnext
  let pair := layers.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
    leftInterior hnext
  have hretained : crossingEdgeFinset G
      (fun vertex => vertex ∈ pair.componentSide boundary.component) =
      pair.primalCutEdges web.annular.cellulation.rotation := by
    calc
      crossingEdgeFinset G
          (fun vertex => vertex ∈ pair.componentSide boundary.component) =
          GoertzelV24FiniteEdgeDeletion.componentCrossingEdges
            (pair.primalCutEdges web.annular.cellulation.rotation)
            boundary.component := by
        ext edge
        rw [mem_crossingEdgeFinset_iff,
          GoertzelV24FiniteEdgeDeletion.mem_componentCrossingEdges_iff]
        simp only [pair.mem_componentSide_iff]
      _ = pair.primalCutEdges web.annular.cellulation.rotation :=
        boundary.component_boundary
  have hcompl := crossingEdgeFinset_compl
    (G := G) (fun vertex => vertex ∈ pair.componentSide boundary.component)
  calc
    (crossingEdgeFinset G (fun vertex => vertex ∈
        sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext)).card =
        (crossingEdgeFinset G
          (fun vertex => vertex ∉ pair.componentSide boundary.component)).card := by
      congr 1
      ext edge
      rw [mem_crossingEdgeFinset_iff, mem_crossingEdgeFinset_iff]
      simp [sourceLocalLayerCellVertexSide, pair, layers, boundary]
    _ = (crossingEdgeFinset G
          (fun vertex => vertex ∈ pair.componentSide boundary.component)).card := by
      rw [hcompl]
    _ = (pair.primalCutEdges web.annular.cellulation.rotation).card := by
      rw [hretained]
    _ = 4 := by
      simpa [pair, layers, LocalLayerPair.cutEdges,
        SeparatedAlignedSimpleDualCrosscuts.primalCutEdges] using
          layers.cutEdges_card_eq_four hunique

/-- A literal Cell side is either cyclic or consists of exactly two vertices.

This is the sharp counting statement behind the coarser six-edge carrier
bound below.  Keeping it named is important for serial composition: on the
noncyclic branch every non-boundary edge of the Cell has the same two
endpoints, so simplicity leaves room for at most one internal edge. -/
theorem sourceLocalLayerCellVertexSide_card_eq_two_or_hasCycleOnSide
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    HasCycleOnSide G (fun vertex => vertex ∈
      sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext) ∨
      (sourceLocalLayerCellVertexSide corridor hunique
        leftInterior hnext).card = 2 := by
  let side := sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext
  have hnonempty : ∃ vertex, vertex ∈ side := by
    let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
      leftInterior hnext
    refine ⟨boundary.removed, ?_⟩
    simpa [side, sourceLocalLayerCellVertexSide] using boundary.removed_not_kept
  have hconnected : (G.induce {vertex | vertex ∈ side}).Connected := by
    let pair :=
      (sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique
    let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
      leftInterior hnext
    have hsideEq : (fun vertex => vertex ∈ side) =
        (fun vertex => vertex ∉ pair.componentSide boundary.component) := by
      funext vertex
      simp [side, sourceLocalLayerCellVertexSide, pair, boundary]
    rw [hsideEq]
    exact sourceLocalLayerPair_cellSide_connected
      corridor hunique leftInterior hnext
  have hdegree : ∀ vertex, vertex ∈ side → G.degree vertex = 3 := by
    intro vertex hvertex
    exact sourceLocalLayerCellVertexSide_degree_eq_three
      corridor hunique leftInterior hnext vertex hvertex
  have hboundary : (crossingEdgeFinset G
      (fun vertex => vertex ∈ side)).card = 4 := by
    simpa [side] using
      sourceLocalLayerCellVertexSide_crossingEdgeFinset_card_eq_four
        corridor hunique leftInterior hnext
  rcases hasCycleOnSide_or_card_eq_two_of_local_cubic_of_connected_of_boundary_card_eq_four
      (fun vertex => vertex ∈ side) hdegree hnonempty hconnected hboundary with
      hcycle | hcard
  · exact .inl hcycle
  · right
    simpa [side, Nat.card_eq_fintype_card] using hcard

/-- On the actual opened source, one literal Cell is either cyclic or has the
desired graph-independent six-edge regional carrier. -/
theorem sourceLocalLayerCellRegion_card_le_six_or_hasCycleOnSide
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    HasCycleOnSide G (fun vertex => vertex ∈
      sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext) ∨
      (vertexSetRegionEdges web.annular.RS
        (sourceLocalLayerCellVertexSide corridor hunique
          leftInterior hnext)).card ≤ 6 := by
  let side := sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext
  have hnonempty : ∃ vertex, vertex ∈ side := by
    let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
      leftInterior hnext
    refine ⟨boundary.removed, ?_⟩
    simpa [side, sourceLocalLayerCellVertexSide] using boundary.removed_not_kept
  have hconnected : (G.induce {vertex | vertex ∈ side}).Connected := by
    let pair :=
      (sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique
    let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
      leftInterior hnext
    have hsideEq : (fun vertex => vertex ∈ side) =
        (fun vertex => vertex ∉ pair.componentSide boundary.component) := by
      funext vertex
      simp [side, sourceLocalLayerCellVertexSide, pair, boundary]
    rw [hsideEq]
    exact sourceLocalLayerPair_cellSide_connected
      corridor hunique leftInterior hnext
  have hdegree : ∀ vertex, vertex ∈ side → G.degree vertex = 3 := by
    intro vertex hvertex
    exact sourceLocalLayerCellVertexSide_degree_eq_three
      corridor hunique leftInterior hnext vertex hvertex
  have hboundary : (crossingEdgeFinset G
      (fun vertex => vertex ∈ side)).card = 4 := by
    simpa [side] using
      sourceLocalLayerCellVertexSide_crossingEdgeFinset_card_eq_four
        corridor hunique leftInterior hnext
  rcases hasCycleOnSide_or_card_eq_two_of_local_cubic_of_connected_of_boundary_card_eq_four
      (fun vertex => vertex ∈ side) hdegree hnonempty hconnected hboundary with
      hcycle | hcard
  · exact .inl hcycle
  · right
    have hsideCard : side.card = 2 := by
      simpa [Nat.card_eq_fintype_card] using hcard
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
      exact hdegree vertex hvertex
    have hle := vertexSetRegionEdges_card_le_three_mul_of_local
      web.annular.RS side hlocalIncident
    change (vertexSetRegionEdges web.annular.RS side).card ≤ 6
    omega

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
