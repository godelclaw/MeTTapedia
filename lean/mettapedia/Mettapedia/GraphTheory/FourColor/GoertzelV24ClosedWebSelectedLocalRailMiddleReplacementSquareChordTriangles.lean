import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareChord
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutCollarChord

/-!
# L1: split a replacement-square chord into two literal triangles

The exact square-bond consumer returns either face-pair multiplicity or an
off-walk chord of the selected four-cycle.  In the chord branch, the generic
four-cycle theorem already proved in the adjacent-pair development constructs
the two simple triangles cut off by that chord.  This module records those
triangles in the source-local replacement-square vocabulary.

This is still facial-dual geometry.  It does not identify either triangle
with the manuscript's primal rotor triangle, choose primal crossings for the
new triangle steps, discharge the parallel-face branch, reroute both rails,
attach end caps, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24SelectedDualCycleSeparator
open GoertzelV24SelectedDualCycleSeparator.SelectedDualCycle
open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

namespace MiddleReplacementShortDualCycle

variable {face : SelectedFace (web := web)}

/-- Pin a specified shared primal edge at the walk position where its two
endpoint faces occur.  This uses the selected-crossing API and needs no
pairwise uniqueness of face intersections. -/
private theorem exists_selectedCycle_with_pinned_shared_edge
    (RS : RotationSystem V G.edgeSet)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start start)
    (hcycle : walk.IsCycle)
    {left right : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (hwalkEdge : s(left, right) ∈ walk.edges)
    {edge : G.edgeSet}
    (hshared : edge ∈ sharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) left.1 right.1) :
    ∃ selected : SelectedDualCycle RS start,
      selected.walk = walk ∧ edge ∈ selected.crossingEdges := by
  rcases List.mem_iff_getElem.mp hwalkEdge with ⟨index, hindex, hget⟩
  let step : Fin walk.length := ⟨index, by simpa using hindex⟩
  let edgeStep : Fin walk.edges.length :=
    Fin.cast walk.length_edges.symm step
  have hget' : walk.edges.get edgeStep = s(left, right) := by
    simpa [edgeStep, step] using hget
  have hpair :
      GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
          (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS)) walk step =
        s(left, right) := by
    rw [← GoertzelV24DualPathTransversal.edges_get_coreDualWalkGraphEdge
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) walk step]
    exact hget'
  rcases (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS))).1 hshared with
    ⟨hinterior, hleft, hright⟩
  change s(walk.getVert step.val, walk.getVert (step.val + 1)) =
    s(left, right) at hpair
  have hstepShared : edge ∈ sharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (walk.getVert step.val).1 (walk.getVert (step.val + 1)).1 := by
    rcases Sym2.eq_iff.mp hpair with horiented | hreversed
    · rcases horiented with ⟨hstepLeft, hstepRight⟩
      apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).2
      exact ⟨hinterior, by simpa [hstepLeft] using hleft,
        by simpa [hstepRight] using hright⟩
    · rcases hreversed with ⟨hstepLeft, hstepRight⟩
      apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).2
      exact ⟨hinterior, by simpa [hstepLeft] using hright,
        by simpa [hstepRight] using hleft⟩
  let selected := SelectedDualCycle.ofWalkWithCrossingAt
    RS walk hcycle step edge hstepShared
  refine ⟨selected, rfl, ?_⟩
  exact (selected.mem_crossingEdges_iff edge).2
    ⟨step, by simp [selected]⟩

/-- The internal bond is a shared interior edge of the two faces in its
literal dual-adjacency packet. -/
theorem SquareBondRealization.InternalDualAdjacency.internal_mem_shared
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (adjacency : bond.InternalDualAdjacency) :
    bond.internalEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      adjacency.leftFace.1 adjacency.rightFace.1 := by
  have hfacesValueNe : adjacency.leftFace.1 ≠ adjacency.rightFace.1 := by
    intro hfaces
    exact adjacency.faces_ne (Subtype.ext hfaces)
  have hinterior : bond.internalEdge ∈ interiorEdgeSupport
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) := by
    apply (mem_interiorEdgeSupport_iff
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).2
    refine ⟨Finset.mem_biUnion.2
      ⟨adjacency.leftFace.1, Finset.mem_univ _, adjacency.internal_mem_left⟩,
      ?_⟩
    exact totalIncidenceCount_eq_two_of_mem_faceBoundary_of_mem_faceBoundary_of_ne
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (orbitFace_incidence_le_two web.annular.RS)
      (Finset.mem_univ _) (Finset.mem_univ _) hfacesValueNe
      adjacency.internal_mem_left adjacency.internal_mem_right
  exact (mem_sharedInteriorEdges_iff
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))).2
      ⟨hinterior, adjacency.internal_mem_left, adjacency.internal_mem_right⟩

/-- The two literal facial-dual triangles produced by an off-walk internal
bond chord of the selected four-cycle. -/
structure SquareBondRealization.InternalDualChordTriangles
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component) where
  chord : bond.InternalDualChord
  firstTriangle : SelectedDualGraph (web := web).Walk
    chord.adjacency.leftFace chord.adjacency.leftFace
  secondTriangle : SelectedDualGraph (web := web).Walk
    chord.adjacency.leftFace chord.adjacency.leftFace
  first_isCycle : firstTriangle.IsCycle
  first_length_eq_three : firstTriangle.length = 3
  second_isCycle : secondTriangle.IsCycle
  second_length_eq_three : secondTriangle.length = 3
  chord_mem_first :
    s(chord.adjacency.leftFace, chord.adjacency.rightFace) ∈
      firstTriangle.edges
  chord_mem_second :
    s(chord.adjacency.leftFace, chord.adjacency.rightFace) ∈
      secondTriangle.edges
  first_support_original : ∀ current ∈ firstTriangle.support,
    current ∈ cycle.walk.support
  second_support_original : ∀ current ∈ secondTriangle.support,
    current ∈ cycle.walk.support
  distinct_side : ∃ firstOnly : Sym2 (SelectedFace (web := web)),
    firstOnly ∈ firstTriangle.edges ∧ firstOnly ∉ secondTriangle.edges

/-- **L1 square-chord local consumer.**  A chord of the exact selected
four-cycle cuts it into two genuine three-cycles. -/
theorem SquareBondRealization.InternalDualChord.exists_triangles
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (chord : bond.InternalDualChord) (hlength : cycle.walk.length = 4) :
    Nonempty bond.InternalDualChordTriangles := by
  rcases
      GoertzelV24DualCycleChord.exists_two_triangles_of_isCycle_of_length_eq_four_of_isChord
        cycle.isCycle hlength chord.isChord with
    ⟨firstTriangle, secondTriangle, hfirstCycle, hfirstLength,
      hsecondCycle, hsecondLength, hfirstChord, hsecondChord,
      hfirstSupport, hsecondSupport, hdistinct⟩
  exact ⟨{
    chord := chord
    firstTriangle := firstTriangle
    secondTriangle := secondTriangle
    first_isCycle := hfirstCycle
    first_length_eq_three := hfirstLength
    second_isCycle := hsecondCycle
    second_length_eq_three := hsecondLength
    chord_mem_first := hfirstChord
    chord_mem_second := hsecondChord
    first_support_original := hfirstSupport
    second_support_original := hsecondSupport
    distinct_side := hdistinct
  }⟩

/-- The two chord triangles equipped with literal selected primal crossings,
both pinned to cross the internal bond on their chord step. -/
structure SquareBondRealization.InternalDualChordSelectedTriangles
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component) where
  triangles : bond.InternalDualChordTriangles
  firstSelected : SelectedDualCycle web.annular.RS
    triangles.chord.adjacency.leftFace
  secondSelected : SelectedDualCycle web.annular.RS
    triangles.chord.adjacency.leftFace
  first_walk_eq : firstSelected.walk = triangles.firstTriangle
  second_walk_eq : secondSelected.walk = triangles.secondTriangle
  first_length_eq_three : firstSelected.walk.length = 3
  second_length_eq_three : secondSelected.walk.length = 3
  internal_mem_first : bond.internalEdge ∈ firstSelected.crossingEdges
  internal_mem_second : bond.internalEdge ∈ secondSelected.crossingEdges

/-- Every face of the first selected chord triangle remains in the literal
interior support of the original replacement square. -/
theorem SquareBondRealization.InternalDualChordSelectedTriangles.first_support_internal
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (selected : bond.InternalDualChordSelectedTriangles)
    (current : SelectedFace (web := web))
    (hcurrent : current ∈ selected.firstSelected.walk.support) :
    current.1 ∈ web.annular.cellulation.interiorFaces := by
  rw [selected.first_walk_eq] at hcurrent
  exact cycle.support_internal current
    (selected.triangles.first_support_original current hcurrent)

/-- Every face of the second selected chord triangle remains in the literal
interior support of the original replacement square. -/
theorem SquareBondRealization.InternalDualChordSelectedTriangles.second_support_internal
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (selected : bond.InternalDualChordSelectedTriangles)
    (current : SelectedFace (web := web))
    (hcurrent : current ∈ selected.secondSelected.walk.support) :
    current.1 ∈ web.annular.cellulation.interiorFaces := by
  rw [selected.second_walk_eq] at hcurrent
  exact cycle.support_internal current
    (selected.triangles.second_support_original current hcurrent)

/-- **L1 selected-triangle consumer.**  Both triangles cut off by the
internal chord can be handed to the existing selected separator machinery,
with the internal bond retained as a literal crossing. -/
theorem SquareBondRealization.InternalDualChordTriangles.exists_selectedTriangles
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (triangles : bond.InternalDualChordTriangles) :
    Nonempty bond.InternalDualChordSelectedTriangles := by
  have hshared := triangles.chord.adjacency.internal_mem_shared
  rcases exists_selectedCycle_with_pinned_shared_edge web.annular.RS
      triangles.firstTriangle triangles.first_isCycle
      triangles.chord_mem_first hshared with
    ⟨firstSelected, hfirstWalk, hfirstInternal⟩
  rcases exists_selectedCycle_with_pinned_shared_edge web.annular.RS
      triangles.secondTriangle triangles.second_isCycle
      triangles.chord_mem_second hshared with
    ⟨secondSelected, hsecondWalk, hsecondInternal⟩
  exact ⟨{
    triangles := triangles
    firstSelected := firstSelected
    secondSelected := secondSelected
    first_walk_eq := hfirstWalk
    second_walk_eq := hsecondWalk
    first_length_eq_three := by
      rw [hfirstWalk]
      exact triangles.first_length_eq_three
    second_length_eq_three := by
      rw [hsecondWalk]
      exact triangles.second_length_eq_three
    internal_mem_first := hfirstInternal
    internal_mem_second := hsecondInternal
  }⟩

end MiddleReplacementShortDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
