import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareChordTriangles
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
    let square := squareDualCycle_of_firstThirdSquare
      (rungs := rungs) hfirst hthird hfaceSecond
    Nonempty (square.SourceChordSelectedTriangles
      (secondPlacement := secondPlacement)) := by
  dsimp only
  let square := squareDualCycle_of_firstThirdSquare
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
        square.cycle.isCycle square.length_eq_four hchord with
    ⟨firstTriangle, secondTriangle, hfirstCycle, hfirstLength,
      hsecondCycle, hsecondLength, hfirstChord, hsecondChord,
      hfirstEdges, hsecondEdges, horiginalEdges, _hfirstSupport,
      _hsecondSupport, _hdistinct⟩
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
  · exact horiginalEdges

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
    let square := squareDualCycle_of_firstThirdSquare
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

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
