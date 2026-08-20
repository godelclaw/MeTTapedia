import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareChord
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutCollarChord

/-!
# L1: split a replacement-square chord into two literal triangles

The exact square-bond consumer returns either face-pair multiplicity or an
off-walk chord of the selected four-cycle.  In the chord branch, the generic
four-cycle theorem already proved in the adjacent-pair development constructs
the two simple triangles cut off by that chord.  This module records those
triangles in the source-local replacement-square vocabulary.

The source-facing selector pins the literal internal bond at the chord step
and reuses the original replacement square's selected crossings at every old
step.  This is still facial-dual geometry.  It does not identify either
triangle with the manuscript's primal rotor triangle, discharge the cyclic or
parallel-face branch, reroute both rails, attach end caps, or close Fable flag
L1.
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

/-- Transport a literal shared primal edge along equality of the underlying
unoriented facial-dual edge. -/
private theorem mem_sharedInteriorEdges_of_sym2_eq
    (RS : RotationSystem V G.edgeSet)
    {firstLeft firstRight secondLeft secondRight : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (hpairs : s(firstLeft, firstRight) = s(secondLeft, secondRight))
    {edge : G.edgeSet}
    (hshared : edge ∈ sharedInteriorEdges
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      secondLeft.1 secondRight.1) :
    edge ∈ sharedInteriorEdges
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      firstLeft.1 firstRight.1 := by
  rcases (mem_sharedInteriorEdges_iff
    (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS))).1 hshared with
    ⟨hinterior, hleft, hright⟩
  apply (mem_sharedInteriorEdges_iff
    (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS))).2
  rcases Sym2.eq_iff.mp hpairs with horiented | hreversed
  · rcases horiented with ⟨hfirstLeft, hfirstRight⟩
    exact ⟨hinterior, by simpa [hfirstLeft] using hleft,
      by simpa [hfirstRight] using hright⟩
  · rcases hreversed with ⟨hfirstLeft, hfirstRight⟩
    exact ⟨hinterior, by simpa [hfirstLeft] using hright,
      by simpa [hfirstRight] using hleft⟩

/-- At every step of a chord-cut subcycle, choose either the new chord
crossing or the already-selected crossing of the original cycle edge. -/
private theorem exists_inherited_or_chord_crossing
    (RS : RotationSystem V G.edgeSet)
    {originalStart smallStart : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (original : SelectedDualCycle RS originalStart)
    (small : (interiorDualGraph
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk smallStart smallStart)
    {chordLeft chordRight : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    {chordEdge : G.edgeSet}
    (hchordShared : chordEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      chordLeft.1 chordRight.1)
    (hedges : ∀ dualEdge ∈ small.edges,
      dualEdge = s(chordLeft, chordRight) ∨ dualEdge ∈ original.walk.edges)
    (step : Fin small.length) :
    let dualEdge :=
      GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) small step
    ∃ edge : G.edgeSet,
      (dualEdge = s(chordLeft, chordRight) → edge = chordEdge) ∧
        (edge = chordEdge ∨ edge ∈ original.crossingEdges) ∧
        edge ∈ sharedInteriorEdges
          (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS))
          (small.getVert step.val).1
          (small.getVert (step.val + 1)).1 := by
  dsimp only
  let dualEdge :=
    GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) small step
  have hdualEdgeMem : dualEdge ∈ small.edges := by
    change
      GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) small step ∈ small.edges
    rw [← GoertzelV24DualPathTransversal.edges_get_coreDualWalkGraphEdge
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) small step]
    exact List.get_mem small.edges _
  by_cases hchord : dualEdge = s(chordLeft, chordRight)
  · refine ⟨chordEdge, fun _ => rfl, .inl rfl, ?_⟩
    apply mem_sharedInteriorEdges_of_sym2_eq RS hchord
    exact hchordShared
  · have horiginal : dualEdge ∈ original.walk.edges :=
      (hedges dualEdge hdualEdgeMem).resolve_left hchord
    rcases List.mem_iff_getElem.mp horiginal with ⟨index, hindex, hget⟩
    let originalStep : Fin original.walk.length :=
      ⟨index, by simpa using hindex⟩
    have hpairs : dualEdge =
        GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
          (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS))
          original.walk originalStep := by
      rw [← GoertzelV24DualPathTransversal.edges_get_coreDualWalkGraphEdge
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) original.walk originalStep]
      simpa [originalStep] using hget.symm
    refine ⟨original.crossingEdge originalStep, ?_, .inr ?_, ?_⟩
    · intro hdual
      exact False.elim (hchord hdual)
    · exact (original.mem_crossingEdges_iff _).2 ⟨originalStep, rfl⟩
    · apply mem_sharedInteriorEdges_of_sym2_eq RS hpairs
      exact original.crossing_mem_shared originalStep

/-- A selected chord subcycle whose old steps inherit the original selected
crossings instead of making fresh arbitrary shared-edge choices. -/
noncomputable def selectedCycleOfOriginalOrChord
    (RS : RotationSystem V G.edgeSet)
    {originalStart smallStart : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (original : SelectedDualCycle RS originalStart)
    (small : (interiorDualGraph
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk smallStart smallStart)
    (hcycle : small.IsCycle)
    {chordLeft chordRight : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    {chordEdge : G.edgeSet}
    (hchordShared : chordEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      chordLeft.1 chordRight.1)
    (hedges : ∀ dualEdge ∈ small.edges,
      dualEdge = s(chordLeft, chordRight) ∨
        dualEdge ∈ original.walk.edges) :
    SelectedDualCycle RS smallStart where
  walk := small
  isCycle := hcycle
  crossingEdge := fun step => Classical.choose
    (exists_inherited_or_chord_crossing RS original small hchordShared
      hedges step)
  crossing_mem_shared := fun step =>
    (Classical.choose_spec
      (exists_inherited_or_chord_crossing RS original small hchordShared
        hedges step)).2.2

/-- Every crossing of the inherited chord subcycle is either the new chord
or one of the original selected crossings. -/
theorem selectedCycleOfOriginalOrChord_crossingEdge_eq_or_mem
    (RS : RotationSystem V G.edgeSet)
    {originalStart smallStart : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (original : SelectedDualCycle RS originalStart)
    (small : (interiorDualGraph
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk smallStart smallStart)
    (hcycle : small.IsCycle)
    {chordLeft chordRight : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    {chordEdge : G.edgeSet}
    (hchordShared : chordEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      chordLeft.1 chordRight.1)
    (hedges : ∀ dualEdge ∈ small.edges,
      dualEdge = s(chordLeft, chordRight) ∨
        dualEdge ∈ original.walk.edges)
    (step : Fin small.length) :
    (selectedCycleOfOriginalOrChord RS original small hcycle hchordShared
      hedges).crossingEdge step = chordEdge ∨
      (selectedCycleOfOriginalOrChord RS original small hcycle hchordShared
        hedges).crossingEdge step ∈ original.crossingEdges := by
  exact (Classical.choose_spec
    (exists_inherited_or_chord_crossing RS original small hchordShared
      hedges step)).2.1

/-- A step whose dual edge is the new chord crosses the specified chord edge
definitionally through the provenance-aware selector. -/
theorem selectedCycleOfOriginalOrChord_crossingEdge_eq_of_coreDualEdge_eq
    (RS : RotationSystem V G.edgeSet)
    {originalStart smallStart : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (original : SelectedDualCycle RS originalStart)
    (small : (interiorDualGraph
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk smallStart smallStart)
    (hcycle : small.IsCycle)
    {chordLeft chordRight : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    {chordEdge : G.edgeSet}
    (hchordShared : chordEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      chordLeft.1 chordRight.1)
    (hedges : ∀ dualEdge ∈ small.edges,
      dualEdge = s(chordLeft, chordRight) ∨
        dualEdge ∈ original.walk.edges)
    (step : Fin small.length)
    (hdual : GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) small step =
        s(chordLeft, chordRight)) :
    (selectedCycleOfOriginalOrChord RS original small hcycle hchordShared
      hedges).crossingEdge step = chordEdge := by
  exact (Classical.choose_spec
    (exists_inherited_or_chord_crossing RS original small hchordShared
      hedges step)).1 hdual

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
  first_edges_original_or_chord : ∀ edge ∈ firstTriangle.edges,
    edge = s(chord.adjacency.leftFace, chord.adjacency.rightFace) ∨
      edge ∈ cycle.walk.edges
  second_edges_original_or_chord : ∀ edge ∈ secondTriangle.edges,
    edge = s(chord.adjacency.leftFace, chord.adjacency.rightFace) ∨
      edge ∈ cycle.walk.edges
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
      hfirstEdges, hsecondEdges, hfirstSupport, hsecondSupport, hdistinct⟩
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
    first_edges_original_or_chord := hfirstEdges
    second_edges_original_or_chord := hsecondEdges
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
  first_crossing_inherited : ∀ step,
    firstSelected.crossingEdge step = bond.internalEdge ∨
      firstSelected.crossingEdge step ∈ cycle.selectedCycle.crossingEdges
  second_crossing_inherited : ∀ step,
    secondSelected.crossingEdge step = bond.internalEdge ∨
      secondSelected.crossingEdge step ∈ cycle.selectedCycle.crossingEdges

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

/-- Repackage the first selected chord triangle as the established short-cycle
separator input, retaining the internal bond as its distinguished crossing. -/
noncomputable def SquareBondRealization.InternalDualChordSelectedTriangles.firstShortCycle
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (selected : bond.InternalDualChordSelectedTriangles) :
    MiddleReplacementShortDualCycle (web := web)
      selected.triangles.chord.adjacency.leftFace := by
  classical
  let anchor := Classical.choose
    ((selected.firstSelected.mem_crossingEdges_iff bond.internalEdge).1
      selected.internal_mem_first)
  have hanchor : selected.firstSelected.crossingEdge anchor =
      bond.internalEdge := Classical.choose_spec
    ((selected.firstSelected.mem_crossingEdges_iff bond.internalEdge).1
      selected.internal_mem_first)
  exact {
    start := selected.triangles.chord.adjacency.leftFace
    walk := selected.firstSelected.walk
    isCycle := selected.firstSelected.isCycle
    length_eq_three_or_four := .inl selected.first_length_eq_three
    face_mem_support := selected.firstSelected.walk.start_mem_support
    support_internal := selected.first_support_internal
    anchor := anchor
    anchorEdge := bond.internalEdge
    anchorEdge_mem_shared := by
      rw [← hanchor]
      exact selected.firstSelected.crossing_mem_shared anchor
  }

/-- Repackage the second selected chord triangle as the established short-cycle
separator input, retaining the internal bond as its distinguished crossing. -/
noncomputable def SquareBondRealization.InternalDualChordSelectedTriangles.secondShortCycle
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (selected : bond.InternalDualChordSelectedTriangles) :
    MiddleReplacementShortDualCycle (web := web)
      selected.triangles.chord.adjacency.leftFace := by
  classical
  let anchor := Classical.choose
    ((selected.secondSelected.mem_crossingEdges_iff bond.internalEdge).1
      selected.internal_mem_second)
  have hanchor : selected.secondSelected.crossingEdge anchor =
      bond.internalEdge := Classical.choose_spec
    ((selected.secondSelected.mem_crossingEdges_iff bond.internalEdge).1
      selected.internal_mem_second)
  exact {
    start := selected.triangles.chord.adjacency.leftFace
    walk := selected.secondSelected.walk
    isCycle := selected.secondSelected.isCycle
    length_eq_three_or_four := .inl selected.second_length_eq_three
    face_mem_support := selected.secondSelected.walk.start_mem_support
    support_internal := selected.second_support_internal
    anchor := anchor
    anchorEdge := bond.internalEdge
    anchorEdge_mem_shared := by
      rw [← hanchor]
      exact selected.secondSelected.crossing_mem_shared anchor
  }

/-- The first chord triangle now reaches the existing selected-separator
component classifier: its inner side is cyclic or a literal one-vertex star. -/
theorem SquareBondRealization.InternalDualChordSelectedTriangles.first_exists_component_cycle_or_star
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (selected : bond.InternalDualChordSelectedTriangles) :
    ∃ triangleComponent :
        (G.deleteEdges (edgeFinsetValueSet
          selected.firstShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
      web.annular.RS.outer.fst ∉ triangleComponent.supp ∧
        (HasCycleOnSide G (fun vertex => vertex ∈ triangleComponent.supp) ∨
          ∃ vertex : V, vertex ∈ triangleComponent.supp ∧
            ∀ edge ∈ selected.firstShortCycle.selectedCycle.crossingEdges,
              vertex ∈ edge.1) := by
  apply selected.firstShortCycle.exists_component_cycle_or_star_of_length_eq_three
  exact selected.first_length_eq_three

/-- The second chord triangle now reaches the existing selected-separator
component classifier: its inner side is cyclic or a literal one-vertex star. -/
theorem SquareBondRealization.InternalDualChordSelectedTriangles.second_exists_component_cycle_or_star
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (selected : bond.InternalDualChordSelectedTriangles) :
    ∃ triangleComponent :
        (G.deleteEdges (edgeFinsetValueSet
          selected.secondShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
      web.annular.RS.outer.fst ∉ triangleComponent.supp ∧
        (HasCycleOnSide G (fun vertex => vertex ∈ triangleComponent.supp) ∨
          ∃ vertex : V, vertex ∈ triangleComponent.supp ∧
            ∀ edge ∈ selected.secondShortCycle.selectedCycle.crossingEdges,
              vertex ∈ edge.1) := by
  apply selected.secondShortCycle.exists_component_cycle_or_star_of_length_eq_three
  exact selected.second_length_eq_three

/-- The star alternative for the first chord triangle is anchored at an
endpoint of the original square's internal bond. -/
theorem SquareBondRealization.InternalDualChordSelectedTriangles.first_exists_component_cycle_or_endpointStar
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (selected : bond.InternalDualChordSelectedTriangles) :
    ∃ triangleComponent :
        (G.deleteEdges (edgeFinsetValueSet
          selected.firstShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
      web.annular.RS.outer.fst ∉ triangleComponent.supp ∧
        (HasCycleOnSide G (fun vertex => vertex ∈ triangleComponent.supp) ∨
          ∃ vertex : V, vertex ∈ triangleComponent.supp ∧
            vertex ∈ bond.internalEdge.1 ∧
            ∀ edge ∈ selected.firstShortCycle.selectedCycle.crossingEdges,
              vertex ∈ edge.1) := by
  rcases selected.first_exists_component_cycle_or_star with
    ⟨triangleComponent, hroot, hcycle | ⟨vertex, hvertex, hall⟩⟩
  · exact ⟨triangleComponent, hroot, .inl hcycle⟩
  · have hinternal : bond.internalEdge ∈
        selected.firstShortCycle.selectedCycle.crossingEdges := by
      simpa [SquareBondRealization.InternalDualChordSelectedTriangles.firstShortCycle]
        using selected.firstShortCycle.anchorEdge_mem_crossingEdges
    exact ⟨triangleComponent, hroot,
      .inr ⟨vertex, hvertex, hall bond.internalEdge hinternal, hall⟩⟩

/-- The star alternative for the second chord triangle is anchored at an
endpoint of the original square's internal bond. -/
theorem SquareBondRealization.InternalDualChordSelectedTriangles.second_exists_component_cycle_or_endpointStar
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (selected : bond.InternalDualChordSelectedTriangles) :
    ∃ triangleComponent :
        (G.deleteEdges (edgeFinsetValueSet
          selected.secondShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
      web.annular.RS.outer.fst ∉ triangleComponent.supp ∧
        (HasCycleOnSide G (fun vertex => vertex ∈ triangleComponent.supp) ∨
          ∃ vertex : V, vertex ∈ triangleComponent.supp ∧
            vertex ∈ bond.internalEdge.1 ∧
            ∀ edge ∈ selected.secondShortCycle.selectedCycle.crossingEdges,
              vertex ∈ edge.1) := by
  rcases selected.second_exists_component_cycle_or_star with
    ⟨triangleComponent, hroot, hcycle | ⟨vertex, hvertex, hall⟩⟩
  · exact ⟨triangleComponent, hroot, .inl hcycle⟩
  · have hinternal : bond.internalEdge ∈
        selected.secondShortCycle.selectedCycle.crossingEdges := by
      simpa [SquareBondRealization.InternalDualChordSelectedTriangles.secondShortCycle]
        using selected.secondShortCycle.anchorEdge_mem_crossingEdges
    exact ⟨triangleComponent, hroot,
      .inr ⟨vertex, hvertex, hall bond.internalEdge hinternal, hall⟩⟩

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
  let firstSelected := selectedCycleOfOriginalOrChord web.annular.RS
    cycle.selectedCycle triangles.firstTriangle triangles.first_isCycle
    hshared triangles.first_edges_original_or_chord
  let secondSelected := selectedCycleOfOriginalOrChord web.annular.RS
    cycle.selectedCycle triangles.secondTriangle triangles.second_isCycle
    hshared triangles.second_edges_original_or_chord
  have hfirstInternal : bond.internalEdge ∈ firstSelected.crossingEdges := by
    rcases List.mem_iff_getElem.mp triangles.chord_mem_first with
      ⟨index, hindex, hget⟩
    let step : Fin triangles.firstTriangle.length :=
      ⟨index, by simpa using hindex⟩
    have hdual :
        GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
          (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS))
          triangles.firstTriangle step =
            s(triangles.chord.adjacency.leftFace,
              triangles.chord.adjacency.rightFace) := by
      rw [← GoertzelV24DualPathTransversal.edges_get_coreDualWalkGraphEdge
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        triangles.firstTriangle step]
      simpa [step] using hget
    have hselected : firstSelected.crossingEdge step = bond.internalEdge := by
      dsimp only [firstSelected]
      exact selectedCycleOfOriginalOrChord_crossingEdge_eq_of_coreDualEdge_eq
        web.annular.RS cycle.selectedCycle triangles.firstTriangle
        triangles.first_isCycle hshared
        triangles.first_edges_original_or_chord step hdual
    exact (firstSelected.mem_crossingEdges_iff _).2 ⟨step, hselected⟩
  have hsecondInternal : bond.internalEdge ∈ secondSelected.crossingEdges := by
    rcases List.mem_iff_getElem.mp triangles.chord_mem_second with
      ⟨index, hindex, hget⟩
    let step : Fin triangles.secondTriangle.length :=
      ⟨index, by simpa using hindex⟩
    have hdual :
        GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
          (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS))
          triangles.secondTriangle step =
            s(triangles.chord.adjacency.leftFace,
              triangles.chord.adjacency.rightFace) := by
      rw [← GoertzelV24DualPathTransversal.edges_get_coreDualWalkGraphEdge
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        triangles.secondTriangle step]
      simpa [step] using hget
    have hselected : secondSelected.crossingEdge step = bond.internalEdge := by
      dsimp only [secondSelected]
      exact selectedCycleOfOriginalOrChord_crossingEdge_eq_of_coreDualEdge_eq
        web.annular.RS cycle.selectedCycle triangles.secondTriangle
        triangles.second_isCycle hshared
        triangles.second_edges_original_or_chord step hdual
    exact (secondSelected.mem_crossingEdges_iff _).2 ⟨step, hselected⟩
  exact ⟨{
    triangles := triangles
    firstSelected := firstSelected
    secondSelected := secondSelected
    first_walk_eq := rfl
    second_walk_eq := rfl
    first_length_eq_three := by
      exact triangles.first_length_eq_three
    second_length_eq_three := by
      exact triangles.second_length_eq_three
    internal_mem_first := hfirstInternal
    internal_mem_second := hsecondInternal
    first_crossing_inherited := by
      intro step
      exact selectedCycleOfOriginalOrChord_crossingEdge_eq_or_mem
        web.annular.RS cycle.selectedCycle triangles.firstTriangle
        triangles.first_isCycle hshared
        triangles.first_edges_original_or_chord step
    second_crossing_inherited := by
      intro step
      exact selectedCycleOfOriginalOrChord_crossingEdge_eq_or_mem
        web.annular.RS cycle.selectedCycle triangles.secondTriangle
        triangles.second_isCycle hshared
        triangles.second_edges_original_or_chord step
  }⟩

end MiddleReplacementShortDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
