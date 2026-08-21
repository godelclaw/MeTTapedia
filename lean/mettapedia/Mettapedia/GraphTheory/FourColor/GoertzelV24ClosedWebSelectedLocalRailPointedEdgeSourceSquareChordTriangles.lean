import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareChordTriangles
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementCrossingSelection
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalCommonNeighborIncidence
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeSourceSquareChordCrossing

/-!
# L1: split the source-square diagonal into selected triangles

The pointed old-forward branch now supplies both a literal chord of the
canonical first--third facial-dual square and the exact centre-to-side primal
edge crossing that chord.  The generic four-cycle chord theorem splits the
square into two simple triangles.  This module equips both triangles with
selected primal crossings: the new chord step uses the retained
centre-to-side edge, and every old square step reuses the source square's
existing selected crossing.

This is a positive source-local construction supporting L1.  It does not yet
classify the two selected triangle separators, perform a rotor/square
reduction, repair or iterate the rails, attach end caps, construct separated
crosscuts, or close L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathPointedOccurrence
open GoertzelV24FaceOrbitIncidence
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24SelectedDualCycleSeparator
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

private abbrev SelectedFace
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {firstInterior : CorridorInterior blockLength}
    {hfirstNext : firstInterior.center.val + 2 < blockLength}
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {secondPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior firstInterior hfirstNext)}
    {thirdPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)}

/-- The two selected triangular separators cut off by the source-square
diagonal.  The chord crossing is retained literally, while all non-chord
steps inherit the original square's selected crossings. -/
structure MiddleReplacementSquareDualCycle.SourceChordSelectedTriangles
    {face : SelectedFace web}
    (square : MiddleReplacementSquareDualCycle (web := web) face) where
  position :
    {position // position ∈ selectedPlacementSidePositions secondPlacement}
  face_eq : face = selectedPlacementSideFace secondPlacement position
  chordEdge : G.edgeSet
  chordEdge_eq : chordEdge = web.annular.RS.edgeOf
    (faceCycleDart web.annular.RS secondPlacement.root position.1)
  chord_mem_shared : chordEdge ∈ sharedInteriorEdges
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))
    (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior firstInterior hfirstNext).center).1
    face.1
  firstSelected : SelectedDualCycle web.annular.RS
    (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior firstInterior hfirstNext).center)
  secondSelected : SelectedDualCycle web.annular.RS
    (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior firstInterior hfirstNext).center)
  first_length_eq_three : firstSelected.walk.length = 3
  second_length_eq_three : secondSelected.walk.length = 3
  chordEdge_mem_first : chordEdge ∈ firstSelected.crossingEdges
  chordEdge_mem_second : chordEdge ∈ secondSelected.crossingEdges
  first_crossing_chord_or_original : ∀ step,
    firstSelected.crossingEdge step = chordEdge ∨
      firstSelected.crossingEdge step ∈ square.cycle.selectedCycle.crossingEdges
  second_crossing_chord_or_original : ∀ step,
    secondSelected.crossingEdge step = chordEdge ∨
      secondSelected.crossingEdge step ∈ square.cycle.selectedCycle.crossingEdges
  first_crossing_at_original : ∀ step originalStep,
    GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        firstSelected.walk step =
      GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        square.cycle.selectedCycle.walk originalStep →
      firstSelected.crossingEdge step =
        square.cycle.selectedCycle.crossingEdge originalStep
  second_crossing_at_original : ∀ step originalStep,
    GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        secondSelected.walk step =
      GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        square.cycle.selectedCycle.walk originalStep →
      secondSelected.crossingEdge step =
        square.cycle.selectedCycle.crossingEdge originalStep
  first_support_original : ∀ current ∈ firstSelected.walk.support,
    current ∈ square.cycle.walk.support
  second_support_original : ∀ current ∈ secondSelected.walk.support,
    current ∈ square.cycle.walk.support
  original_edges_covered : ∀ dualEdge ∈ square.cycle.walk.edges,
    dualEdge ∈ firstSelected.walk.edges ∨
      dualEdge ∈ secondSelected.walk.edges

namespace MiddleReplacementSquareDualCycle.SourceChordSelectedTriangles

/-- A chord occurrence in a subcycle forces the specified primal chord edge
into the selected crossing support built by the provenance-aware selector. -/
private theorem chordEdge_mem_selectedCycleOfOriginalOrChord
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
    (hchordNotOriginal : s(chordLeft, chordRight) ∉ original.walk.edges)
    (hedges : ∀ dualEdge ∈ small.edges,
      dualEdge = s(chordLeft, chordRight) ∨
        dualEdge ∈ original.walk.edges)
    (hchordMem : s(chordLeft, chordRight) ∈ small.edges) :
    chordEdge ∈
      (MiddleReplacementShortDualCycle.selectedCycleOfOriginalOrChord
        RS original small hcycle hchordShared hchordNotOriginal hedges).crossingEdges := by
  rcases List.mem_iff_getElem.mp hchordMem with ⟨index, hindex, hget⟩
  let step : Fin small.length := ⟨index, by simpa using hindex⟩
  have hdual :
      GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
          (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS)) small step =
        s(chordLeft, chordRight) := by
    rw [← GoertzelV24DualPathTransversal.edges_get_coreDualWalkGraphEdge
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) small step]
    simpa [step] using hget
  apply (SelectedDualCycle.mem_crossingEdges_iff _ chordEdge).2
  refine ⟨step, ?_⟩
  exact MiddleReplacementShortDualCycle.selectedCycleOfOriginalOrChord_crossingEdge_eq_of_coreDualEdge_eq
    RS original small hcycle hchordShared hchordNotOriginal hedges step hdual

end MiddleReplacementSquareDualCycle.SourceChordSelectedTriangles

/-- **L1 selected source-square chord triangles.**  An actual old-forward
pointed origin constructs two length-three selected dual cycles.  Their new
step crosses the literal centre-to-side edge, and every other crossing is
inherited from the canonical source square. -/
theorem SelectedPlacementSideForwardEdgeReceipt.exists_sourceSquare_chordSelectedTriangles
    {left right :
      {position // position ∈ selectedPlacementSidePositions secondPlacement}}
    {edge : Sym2 (SelectedFace web)}
    (receipt : SelectedPlacementSideForwardEdgeReceipt
      secondPlacement left right edge)
    {face : SelectedFace web}
    (hfirst : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hthird : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    (hface : face = selectedPlacementSideFace secondPlacement left ∨
      face = selectedPlacementSideFace secondPlacement right) :
    let square := MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
      (rungs := rungs) hfirst hthird hfaceSecond
    Nonempty (square.SourceChordSelectedTriangles
      (secondPlacement := secondPlacement)) := by
  dsimp only
  let square := MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
    (rungs := rungs) hfirst hthird hfaceSecond
  rcases
      Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.exists_sourceSquare_secondFace_chordCrossing
        receipt hfirst hthird hfaceSecond hface with
    ⟨position, hposition, hchordShared, hchord⟩
  let chordEdge : G.edgeSet := web.annular.RS.edgeOf
    (faceCycleDart web.annular.RS secondPlacement.root position.1)
  let secondFace :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior firstInterior hfirstNext).center
  rcases
      GoertzelV24DualCycleChord.exists_two_triangles_of_isCycle_of_length_eq_four_of_isChord
        square.cycle.isCycle square.length_eq_four (by
          change (squareDualCycle_of_firstThirdSquare (rungs := rungs)
            hfirst hthird hfaceSecond).cycle.walk.IsChord
              s(secondFace, face)
          exact hchord) with
    ⟨firstTriangle, secondTriangle, hfirstCycle, hfirstLength,
      hsecondCycle, hsecondLength, hfirstChord, hsecondChord,
      hfirstEdges, hsecondEdges, horiginalEdges, hfirstSupport,
      hsecondSupport, _hdistinct⟩
  have hchordNotOriginal : s(secondFace, face) ∉ square.cycle.walk.edges :=
    (SimpleGraph.Walk.isChord_sym2Mk.1 hchord).2.1
  let firstSelected :=
    MiddleReplacementShortDualCycle.selectedCycleOfOriginalOrChord
      web.annular.RS square.cycle.selectedCycle firstTriangle hfirstCycle
        hchordShared hchordNotOriginal hfirstEdges
  let secondSelected :=
    MiddleReplacementShortDualCycle.selectedCycleOfOriginalOrChord
      web.annular.RS square.cycle.selectedCycle secondTriangle hsecondCycle
        hchordShared hchordNotOriginal hsecondEdges
  refine ⟨{
    position := position
    face_eq := hposition
    chordEdge := chordEdge
    chordEdge_eq := rfl
    chord_mem_shared := hchordShared
    firstSelected := firstSelected
    secondSelected := secondSelected
    first_length_eq_three := ?_
    second_length_eq_three := ?_
    chordEdge_mem_first := ?_
    chordEdge_mem_second := ?_
    first_crossing_chord_or_original := ?_
    second_crossing_chord_or_original := ?_
    first_crossing_at_original := ?_
    second_crossing_at_original := ?_
    first_support_original := ?_
    second_support_original := ?_
    original_edges_covered := ?_
  }⟩
  · exact hfirstLength
  · exact hsecondLength
  · exact MiddleReplacementSquareDualCycle.SourceChordSelectedTriangles.chordEdge_mem_selectedCycleOfOriginalOrChord
      web.annular.RS square.cycle.selectedCycle firstTriangle hfirstCycle
        hchordShared hchordNotOriginal hfirstEdges hfirstChord
  · exact MiddleReplacementSquareDualCycle.SourceChordSelectedTriangles.chordEdge_mem_selectedCycleOfOriginalOrChord
      web.annular.RS square.cycle.selectedCycle secondTriangle hsecondCycle
        hchordShared hchordNotOriginal hsecondEdges hsecondChord
  · intro step
    exact MiddleReplacementShortDualCycle.selectedCycleOfOriginalOrChord_crossingEdge_eq_or_mem
      web.annular.RS square.cycle.selectedCycle firstTriangle hfirstCycle
        hchordShared hchordNotOriginal hfirstEdges step
  · intro step
    exact MiddleReplacementShortDualCycle.selectedCycleOfOriginalOrChord_crossingEdge_eq_or_mem
      web.annular.RS square.cycle.selectedCycle secondTriangle hsecondCycle
        hchordShared hchordNotOriginal hsecondEdges step
  · intro step originalStep hdual
    exact MiddleReplacementShortDualCycle.selectedCycleOfOriginalOrChord_crossingEdge_eq_of_coreDualEdge_eq_original
      web.annular.RS square.cycle.selectedCycle firstTriangle hfirstCycle
        hchordShared hchordNotOriginal hfirstEdges step originalStep hdual
  · intro step originalStep hdual
    exact MiddleReplacementShortDualCycle.selectedCycleOfOriginalOrChord_crossingEdge_eq_of_coreDualEdge_eq_original
      web.annular.RS square.cycle.selectedCycle secondTriangle hsecondCycle
        hchordShared hchordNotOriginal hsecondEdges step originalStep hdual
  · exact hfirstSupport
  · exact hsecondSupport
  · exact horiginalEdges

namespace MiddleReplacementSquareDualCycle.SourceChordSelectedTriangles

variable {face : SelectedFace web}
  {square : MiddleReplacementSquareDualCycle (web := web) face}

/-- Every selected crossing of the reselected source square survives in one
of its two chord triangles at the corresponding dual step. -/
theorem original_crossing_covered
    (selected : square.SourceChordSelectedTriangles
      (secondPlacement := secondPlacement))
    (originalStep : Fin square.cycle.selectedCycle.walk.length) :
    (∃ firstStep : Fin selected.firstSelected.walk.length,
      selected.firstSelected.crossingEdge firstStep =
        square.cycle.selectedCycle.crossingEdge originalStep) ∨
      ∃ secondStep : Fin selected.secondSelected.walk.length,
        selected.secondSelected.crossingEdge secondStep =
          square.cycle.selectedCycle.crossingEdge originalStep := by
  let originalDual :=
    GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      square.cycle.selectedCycle.walk originalStep
  have horiginalMem : originalDual ∈ square.cycle.selectedCycle.walk.edges := by
    change
      GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        square.cycle.selectedCycle.walk originalStep ∈
          square.cycle.selectedCycle.walk.edges
    rw [← GoertzelV24DualPathTransversal.edges_get_coreDualWalkGraphEdge
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      square.cycle.selectedCycle.walk originalStep]
    exact List.get_mem square.cycle.selectedCycle.walk.edges _
  rcases selected.original_edges_covered originalDual horiginalMem with
    hfirst | hsecond
  · rcases List.mem_iff_getElem.mp hfirst with ⟨index, hindex, hget⟩
    let firstStep : Fin selected.firstSelected.walk.length :=
      ⟨index, by simpa using hindex⟩
    have hdual :
        GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
            (orbitFaceBoundary web.annular.RS)
            (Finset.univ : Finset (OrbitFace web.annular.RS))
            selected.firstSelected.walk firstStep = originalDual := by
      rw [← GoertzelV24DualPathTransversal.edges_get_coreDualWalkGraphEdge
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        selected.firstSelected.walk firstStep]
      simpa [firstStep] using hget
    exact .inl ⟨firstStep,
      selected.first_crossing_at_original firstStep originalStep hdual⟩
  · rcases List.mem_iff_getElem.mp hsecond with ⟨index, hindex, hget⟩
    let secondStep : Fin selected.secondSelected.walk.length :=
      ⟨index, by simpa using hindex⟩
    have hdual :
        GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
            (orbitFaceBoundary web.annular.RS)
            (Finset.univ : Finset (OrbitFace web.annular.RS))
            selected.secondSelected.walk secondStep = originalDual := by
      rw [← GoertzelV24DualPathTransversal.edges_get_coreDualWalkGraphEdge
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        selected.secondSelected.walk secondStep]
      simpa [secondStep] using hget
    exact .inr ⟨secondStep,
      selected.second_crossing_at_original secondStep originalStep hdual⟩

/-- One selected chord triangle retains the literal outgoing rung of the
middle Cell--3 placement.  This uses the reselected source square; the same
statement is not available from an arbitrary crossing selection on the same
facial walk. -/
theorem secondRung_covered
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {face : SelectedFace web}
    (hfirst : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hthird : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    (selected :
      (MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
        (rungs := rungs) hfirst hthird hfaceSecond).SourceChordSelectedTriangles
          (secondPlacement := secondPlacement)) :
    (∃ firstStep : Fin selected.firstSelected.walk.length,
      selected.firstSelected.crossingEdge firstStep =
        rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing) ∨
      ∃ secondStep : Fin selected.secondSelected.walk.length,
        selected.secondSelected.crossingEdge secondStep =
          rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing := by
  let original := squareDualCycle_of_firstThirdSquare
    (rungs := rungs) hfirst hthird hfaceSecond
  let square := MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
    (rungs := rungs) hfirst hthird hfaceSecond
  let secondStep := MiddleReplacementShortDualCycle.squareSecondStep original
  have hedge : square.cycle.selectedCycle.crossingEdge secondStep =
      rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing := by
    change
      (MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
        (rungs := rungs) hfirst hthird hfaceSecond).cycle.crossingEdge
          (MiddleReplacementShortDualCycle.squareSecondStep
            (squareDualCycle_of_firstThirdSquare (rungs := rungs)
              hfirst hthird hfaceSecond)) = _
    exact
      MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung_crossingEdge_secondStep
        (rungs := rungs) hfirst hthird hfaceSecond
  rcases selected.original_crossing_covered secondStep with
    ⟨firstStep, hfirstEdge⟩ | ⟨secondStep', hsecondEdge⟩
  · exact .inl ⟨firstStep, hfirstEdge.trans hedge⟩
  · exact .inr ⟨secondStep', hsecondEdge.trans hedge⟩

/-- A one-vertex chord-triangle component incident to the retained middle
source rung supplies the exact pointwise incidence consumed by the literal
successor bridge. -/
private theorem commonNeighborVertexIncidenceAt_of_chordStar
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {thirdPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)}
    {face : SelectedFace web}
    {square : MiddleReplacementSquareDualCycle (web := web) face}
    (successor : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement)
    (hsecond : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hthird : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (selected : square.SourceChordSelectedTriangles
      (secondPlacement := secondPlacement))
    (crossingEdges : Finset G.edgeSet)
    (hrung : rungs.edge
      (nextCorridorInterior firstInterior hfirstNext).outgoing ∈ crossingEdges)
    (vertex : V)
    (hvertexChord : vertex ∈ selected.chordEdge.1)
    (hall : ∀ edge ∈ crossingEdges, vertex ∈ edge.1) :
    successor.CommonNeighborVertexIncidenceAt face hsecond hthird := by
  have hshared := (mem_sharedInteriorEdges_iff
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))).1
      selected.chord_mem_shared
  refine ⟨selected.chordEdge, hshared.2.1, hshared.2.2, vertex, ?_, ?_⟩
  · apply
      (GoertzelV24RotationVertexCutProfile.mem_simpleGraphRotationSystem_endpoints_iff
        web.annular.cellulation.rotation _ vertex).2
    change vertex ∈
      (faceCycleEdge web.annular.RS secondPlacement.root
        secondPlacement.outgoingPosition : G.edgeSet).1
    rw [secondPlacement.outgoing_edge]
    exact hall _ hrung
  · apply
      (GoertzelV24RotationVertexCutProfile.mem_simpleGraphRotationSystem_endpoints_iff
        web.annular.cellulation.rotation _ vertex).2
    exact hvertexChord

/-- Every face of the first selected source-square triangle remains in the
literal interior support of the original square. -/
theorem first_support_internal
    (selected : square.SourceChordSelectedTriangles
      (secondPlacement := secondPlacement))
    (current : SelectedFace web)
    (hcurrent : current ∈ selected.firstSelected.walk.support) :
    current.1 ∈ web.annular.cellulation.interiorFaces :=
  square.cycle.support_internal current
    (selected.first_support_original current hcurrent)

/-- Every face of the second selected source-square triangle remains in the
literal interior support of the original square. -/
theorem second_support_internal
    (selected : square.SourceChordSelectedTriangles
      (secondPlacement := secondPlacement))
    (current : SelectedFace web)
    (hcurrent : current ∈ selected.secondSelected.walk.support) :
    current.1 ∈ web.annular.cellulation.interiorFaces :=
  square.cycle.support_internal current
    (selected.second_support_original current hcurrent)

/-- Repackage the first selected source-square triangle as the established
short-cycle separator, anchored at the literal chord crossing. -/
noncomputable def firstShortCycle
    (selected : square.SourceChordSelectedTriangles
      (secondPlacement := secondPlacement)) :
    MiddleReplacementShortDualCycle (web := web)
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) := by
  classical
  let anchor := Classical.choose
    ((selected.firstSelected.mem_crossingEdges_iff selected.chordEdge).1
      selected.chordEdge_mem_first)
  have hanchor : selected.firstSelected.crossingEdge anchor =
      selected.chordEdge := Classical.choose_spec
    ((selected.firstSelected.mem_crossingEdges_iff selected.chordEdge).1
      selected.chordEdge_mem_first)
  exact {
    start :=
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center
    walk := selected.firstSelected.walk
    isCycle := selected.firstSelected.isCycle
    length_eq_three_or_four := .inl selected.first_length_eq_three
    face_mem_support := selected.firstSelected.walk.start_mem_support
    support_internal := selected.first_support_internal
    anchor := anchor
    anchorEdge := selected.chordEdge
    anchorEdge_mem_shared := by
      rw [← hanchor]
      exact selected.firstSelected.crossing_mem_shared anchor
    crossingEdge := selected.firstSelected.crossingEdge
    crossing_mem_shared := selected.firstSelected.crossing_mem_shared
    crossingEdge_anchor := hanchor
  }

/-- Repackage the second selected source-square triangle as the established
short-cycle separator, anchored at the same literal chord crossing. -/
noncomputable def secondShortCycle
    (selected : square.SourceChordSelectedTriangles
      (secondPlacement := secondPlacement)) :
    MiddleReplacementShortDualCycle (web := web)
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) := by
  classical
  let anchor := Classical.choose
    ((selected.secondSelected.mem_crossingEdges_iff selected.chordEdge).1
      selected.chordEdge_mem_second)
  have hanchor : selected.secondSelected.crossingEdge anchor =
      selected.chordEdge := Classical.choose_spec
    ((selected.secondSelected.mem_crossingEdges_iff selected.chordEdge).1
      selected.chordEdge_mem_second)
  exact {
    start :=
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center
    walk := selected.secondSelected.walk
    isCycle := selected.secondSelected.isCycle
    length_eq_three_or_four := .inl selected.second_length_eq_three
    face_mem_support := selected.secondSelected.walk.start_mem_support
    support_internal := selected.second_support_internal
    anchor := anchor
    anchorEdge := selected.chordEdge
    anchorEdge_mem_shared := by
      rw [← hanchor]
      exact selected.secondSelected.crossing_mem_shared anchor
    crossingEdge := selected.secondSelected.crossingEdge
    crossing_mem_shared := selected.secondSelected.crossing_mem_shared
    crossingEdge_anchor := hanchor
  }

/-- The first selected source-square triangle reaches the generic separator
classifier.  Its inner side is cyclic or a one-vertex star incident to the
literal chord crossing and every selected boundary edge. -/
theorem first_exists_component_cycle_or_chordStar
    (selected : square.SourceChordSelectedTriangles
      (secondPlacement := secondPlacement)) :
    ∃ component :
        (G.deleteEdges (edgeFinsetValueSet
          selected.firstShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
      web.annular.RS.outer.fst ∉ component.supp ∧
        (HasCycleOnSide G (fun vertex => vertex ∈ component.supp) ∨
          ∃ vertex : V, vertex ∈ component.supp ∧
            vertex ∈ selected.chordEdge.1 ∧
            ∀ edge ∈ selected.firstShortCycle.selectedCycle.crossingEdges,
              vertex ∈ edge.1) := by
  rcases selected.firstShortCycle.exists_component_cycle_or_star_of_length_eq_three
      selected.first_length_eq_three with
    ⟨component, hroot, hcycle | ⟨vertex, hvertex, hall⟩⟩
  · exact ⟨component, hroot, .inl hcycle⟩
  · have hchord : selected.chordEdge ∈
        selected.firstShortCycle.selectedCycle.crossingEdges := by
      simpa [firstShortCycle] using
        selected.firstShortCycle.anchorEdge_mem_crossingEdges
    exact ⟨component, hroot,
      .inr ⟨vertex, hvertex, hall selected.chordEdge hchord, hall⟩⟩

/-- The second selected source-square triangle has the same cyclic-or-star
classification, anchored at the same literal chord crossing. -/
theorem second_exists_component_cycle_or_chordStar
    (selected : square.SourceChordSelectedTriangles
      (secondPlacement := secondPlacement)) :
    ∃ component :
        (G.deleteEdges (edgeFinsetValueSet
          selected.secondShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
      web.annular.RS.outer.fst ∉ component.supp ∧
        (HasCycleOnSide G (fun vertex => vertex ∈ component.supp) ∨
          ∃ vertex : V, vertex ∈ component.supp ∧
            vertex ∈ selected.chordEdge.1 ∧
            ∀ edge ∈ selected.secondShortCycle.selectedCycle.crossingEdges,
              vertex ∈ edge.1) := by
  rcases selected.secondShortCycle.exists_component_cycle_or_star_of_length_eq_three
      selected.second_length_eq_three with
    ⟨component, hroot, hcycle | ⟨vertex, hvertex, hall⟩⟩
  · exact ⟨component, hroot, .inl hcycle⟩
  · have hchord : selected.chordEdge ∈
        selected.secondShortCycle.selectedCycle.crossingEdges := by
      simpa [secondShortCycle] using
        selected.secondShortCycle.anchorEdge_mem_crossingEdges
    exact ⟨component, hroot,
      .inr ⟨vertex, hvertex, hall selected.chordEdge hchord, hall⟩⟩

/-- **L1 selected source-square separator reduction.**  After retaining the
literal middle source rung, one chord triangle either has a cyclic inner side
or its one-vertex star constructs the pointwise common-neighbour incidence
needed by the adjacent selected-rail bridge.

The cyclic alternatives remain explicit.  No closed minimality property is
imported into the opened annular carrier. -/
theorem exists_chordTriangle_cycle_or_commonNeighborVertexIncidenceAt
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {face : SelectedFace web}
    (hfirst : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hsecond : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hthird : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    (successor : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement)
    (selected :
      (MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
        (rungs := rungs) hfirst hthird hfaceSecond).SourceChordSelectedTriangles
          (secondPlacement := secondPlacement)) :
    (∃ component :
        (G.deleteEdges (edgeFinsetValueSet
          selected.firstShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
      web.annular.RS.outer.fst ∉ component.supp ∧
        HasCycleOnSide G (fun vertex => vertex ∈ component.supp)) ∨
      (∃ component :
        (G.deleteEdges (edgeFinsetValueSet
          selected.secondShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
      web.annular.RS.outer.fst ∉ component.supp ∧
        HasCycleOnSide G (fun vertex => vertex ∈ component.supp)) ∨
      successor.CommonNeighborVertexIncidenceAt face hsecond hthird := by
  rcases selected.secondRung_covered hfirst hthird hfaceSecond with
    ⟨firstStep, hfirstRung⟩ | ⟨secondStep, hsecondRung⟩
  · rcases selected.first_exists_component_cycle_or_chordStar with
      ⟨component, hroot, hcycle | ⟨vertex, _hvertex, hchord, hall⟩⟩
    · exact .inl ⟨component, hroot, hcycle⟩
    · right
      right
      apply commonNeighborVertexIncidenceAt_of_chordStar successor hsecond hthird
        selected selected.firstSelected.crossingEdges
      · exact (selected.firstSelected.mem_crossingEdges_iff _).2
          ⟨firstStep, hfirstRung⟩
      · exact hchord
      · exact hall
  · rcases selected.second_exists_component_cycle_or_chordStar with
      ⟨component, hroot, hcycle | ⟨vertex, _hvertex, hchord, hall⟩⟩
    · exact .inr (.inl ⟨component, hroot, hcycle⟩)
    · right
      right
      apply commonNeighborVertexIncidenceAt_of_chordStar successor hsecond hthird
        selected selected.secondSelected.crossingEdges
      · exact (selected.secondSelected.mem_crossingEdges_iff _).2
          ⟨secondStep, hsecondRung⟩
      · exact hchord
      · exact hall

/-- If the collision face is known not to be either literal flank of the
middle placement, the star branch is impossible and one of the two selected
chord triangles has a cyclic inner side. -/
theorem exists_chordTriangle_cycle_of_face_ne_flanks
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {face : SelectedFace web}
    (hfirst : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hsecond : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hthird : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    (successor : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement)
    (selected :
      (MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
        (rungs := rungs) hfirst hthird hfaceSecond).SourceChordSelectedTriangles
          (secondPlacement := secondPlacement))
    (hneBefore : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftBefore)
    (hneAfter : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftAfter) :
    (∃ component :
        (G.deleteEdges (edgeFinsetValueSet
          selected.firstShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
      web.annular.RS.outer.fst ∉ component.supp ∧
        HasCycleOnSide G (fun vertex => vertex ∈ component.supp)) ∨
      ∃ component :
        (G.deleteEdges (edgeFinsetValueSet
          selected.secondShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
      web.annular.RS.outer.fst ∉ component.supp ∧
        HasCycleOnSide G (fun vertex => vertex ∈ component.supp) := by
  rcases selected.exists_chordTriangle_cycle_or_commonNeighborVertexIncidenceAt
      hfirst hsecond hthird hfaceSecond successor with
    hfirstCycle | hsecondCycle | hincidence
  · exact .inl hfirstCycle
  · exact .inr hsecondCycle
  · rcases successor.face_eq_before_or_after_of_commonNeighborVertexIncidenceAt
        face hsecond hthird hincidence with hbefore | hafter
    · exact False.elim (hneBefore hbefore)
    · exact False.elim (hneAfter hafter)

end MiddleReplacementSquareDualCycle.SourceChordSelectedTriangles

/-- **L1 pointed source-square reduction with selected geometry.**  The
actual pointed allocation now returns constructed selected chord triangles,
not merely an abstract chord, or one of the three residual
successor/old-centre origin rows. -/
theorem InteriorOccurrence.SelectedAdjacentPointedFaceAllocation.exists_sourceSquare_chordSelectedTriangles_or_three_origin_rows
    {start finish face : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    {occurrence : InteriorOccurrence (current := face) walk}
    (allocation : InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
      occurrence)
    (hpath : walk.IsPath)
    (hfirst : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hthird : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    let square := MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
      (rungs := rungs) hfirst hthird hfaceSecond
    Nonempty (square.SourceChordSelectedTriangles
        (secondPlacement := secondPlacement)) ∨
      ((allocation.incomingOrigin.IsSuccessorForward ∧
          allocation.outgoingOrigin.IsSuccessorForward) ∨
        (allocation.incomingOrigin.IsSuccessorForward ∧
          allocation.outgoingOrigin.IsOldCenter) ∨
        (allocation.incomingOrigin.IsOldCenter ∧
          allocation.outgoingOrigin.IsSuccessorForward)) := by
  dsimp only
  generalize hincoming : allocation.incomingOrigin = incomingOrigin
  cases incomingOrigin with
  | oldForward incomingLeft incomingRight incomingSuccessor incomingStep =>
      left
      have hfaces := allocation.incomingFaces
      rw [hincoming] at hfaces
      have hface : face = selectedPlacementSideFace secondPlacement incomingLeft ∨
          face = selectedPlacementSideFace secondPlacement incomingRight := by
        rcases hfaces with hfaces | hfaces
        · exact .inr hfaces.2
        · exact .inl hfaces.2
      exact
        Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.exists_sourceSquare_chordSelectedTriangles
          incomingStep hfirst hthird hfaceSecond hface
  | successorForward incomingLeft incomingRight incomingSuccessor incomingStep =>
      generalize houtgoing : allocation.outgoingOrigin = outgoingOrigin
      cases outgoingOrigin with
      | oldForward outgoingLeft outgoingRight outgoingSuccessor outgoingStep =>
          left
          have hfaces := allocation.outgoingFaces
          rw [houtgoing] at hfaces
          have hface :
              face = selectedPlacementSideFace secondPlacement outgoingLeft ∨
                face = selectedPlacementSideFace secondPlacement outgoingRight := by
            rcases hfaces with hfaces | hfaces
            · exact .inl hfaces.1
            · exact .inr hfaces.1
          exact
            Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.exists_sourceSquare_chordSelectedTriangles
              outgoingStep hfirst hthird hfaceSecond hface
      | successorForward outgoingLeft outgoingRight outgoingSuccessor outgoingStep =>
          right
          exact .inl
            ⟨by simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsSuccessorForward],
              by simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsSuccessorForward]⟩
      | oldCenter outgoingPosition outgoingStep =>
          right
          exact .inr (.inl
            ⟨by simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsSuccessorForward],
              by simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsOldCenter]⟩)
  | oldCenter incomingPosition incomingStep =>
      generalize houtgoing : allocation.outgoingOrigin = outgoingOrigin
      cases outgoingOrigin with
      | oldForward outgoingLeft outgoingRight outgoingSuccessor outgoingStep =>
          left
          have hfaces := allocation.outgoingFaces
          rw [houtgoing] at hfaces
          have hface :
              face = selectedPlacementSideFace secondPlacement outgoingLeft ∨
                face = selectedPlacementSideFace secondPlacement outgoingRight := by
            rcases hfaces with hfaces | hfaces
            · exact .inl hfaces.1
            · exact .inr hfaces.1
          exact
            Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.exists_sourceSquare_chordSelectedTriangles
              outgoingStep hfirst hthird hfaceSecond hface
      | successorForward outgoingLeft outgoingRight outgoingSuccessor outgoingStep =>
          right
          exact .inr (.inr
            ⟨by simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsOldCenter],
              by simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsSuccessorForward]⟩)
      | oldCenter outgoingPosition outgoingStep =>
          exact False.elim
            (InteriorOccurrence.not_both_incident_edges_oldCenter
              occurrence hpath incomingPosition incomingStep
                outgoingPosition outgoingStep hfaceSecond)

/-- **L1 producer-to-consumer source-square reduction.**  For an actual
pointed allocation at a non-flank collision, the old-forward rows construct a
selected chord triangle with a cyclic inner side.  The only other outcomes are
the three explicit successor/old-centre origin rows.

This theorem checks that the chord construction, selected crossing provenance,
component classifier, and local common-neighbour consumer compose end to end.
It does not discharge the cyclic separator or any of the three residual rows. -/
theorem InteriorOccurrence.SelectedAdjacentPointedFaceAllocation.exists_sourceSquare_chordTriangleCycle_or_three_origin_rows
    {start finish face : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    {occurrence : InteriorOccurrence (current := face) walk}
    (allocation : InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
      occurrence)
    (hpath : walk.IsPath)
    (hfirst : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hsecond : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hthird : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    (successor : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement)
    (hneBefore : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftBefore)
    (hneAfter : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftAfter) :
    let square := MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
      (rungs := rungs) hfirst hthird hfaceSecond
    (∃ selected : square.SourceChordSelectedTriangles
        (secondPlacement := secondPlacement),
      (∃ component :
          (G.deleteEdges (edgeFinsetValueSet
            selected.firstShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
        web.annular.RS.outer.fst ∉ component.supp ∧
          HasCycleOnSide G (fun vertex => vertex ∈ component.supp)) ∨
        ∃ component :
          (G.deleteEdges (edgeFinsetValueSet
            selected.secondShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
        web.annular.RS.outer.fst ∉ component.supp ∧
          HasCycleOnSide G (fun vertex => vertex ∈ component.supp)) ∨
      ((allocation.incomingOrigin.IsSuccessorForward ∧
          allocation.outgoingOrigin.IsSuccessorForward) ∨
        (allocation.incomingOrigin.IsSuccessorForward ∧
          allocation.outgoingOrigin.IsOldCenter) ∨
        (allocation.incomingOrigin.IsOldCenter ∧
          allocation.outgoingOrigin.IsSuccessorForward)) := by
  dsimp only
  rcases allocation.exists_sourceSquare_chordSelectedTriangles_or_three_origin_rows
      hpath hfirst hthird hfaceSecond with hselected | hrows
  · rcases hselected with ⟨selected⟩
    left
    refine ⟨selected, ?_⟩
    exact selected.exists_chordTriangle_cycle_of_face_ne_flanks
      hfirst hsecond hthird hfaceSecond successor hneBefore hneAfter
  · exact .inr hrows

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
