import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalDualTriangleClassification
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorSkeleton

/-!
# L1 classification of a two-step dual collision

The finite local classification in Lean flag L1 has one genuinely bounded
case not removed by corridor geodesicity.  Two facial-dual vertices at
distance two have their displayed middle face as a common neighbour, but they
may a priori have another common neighbour.  The four displayed adjacencies
then form a literal dual four-cycle.

In a graph-backed vertex-minimal Tait counterexample, cyclic five-edge
connectivity turns that four-cycle into an adjacent-pair primal collar with a
dual chord between opposite positions.  If the two corridor endpoints are
not adjacent, that chord can only join the middle face to the extra common
neighbour.  Thus the possible collision is not arbitrary: it lies in the
bounded adjacent-pair collar geometry already isolated by the source.

This is a closed-map L1 classification theorem.  It neither constructs the
cut-open Cell-3 annulus nor assumes that the open carrier is globally cubic.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MinimalDualFourCycleClassification

open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24MinimalFaceIntersections
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

local instance minimalDualFourCycleLocallyFinite : G.LocallyFinite :=
  collarFiniteGraphLocallyFinite G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The facial-dual four-cycle obtained from two distinct common neighbours
of the same nonadjacent endpoint pair. -/
def dualFourCycleWalk
    (graphData : Data G)
    {first middle last other : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (hfirstMiddle : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj first middle)
    (hmiddleLast : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj middle last)
    (hlastOther : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj last other)
    (hotherFirst : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj other first) :
    (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Walk first first :=
  .cons hfirstMiddle
    (.cons hmiddleLast (.cons hlastOther (.cons hotherFirst .nil)))

@[simp] theorem dualFourCycleWalk_length
    (graphData : Data G)
    {first middle last other : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (hfirstMiddle : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj first middle)
    (hmiddleLast : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj middle last)
    (hlastOther : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj last other)
    (hotherFirst : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj other first) :
    (dualFourCycleWalk graphData hfirstMiddle hmiddleLast hlastOther
      hotherFirst).length = 4 := by
  simp [dualFourCycleWalk]

theorem dualFourCycleWalk_isCycle
    (graphData : Data G)
    {first middle last other : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (hfirstMiddle : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj first middle)
    (hmiddleLast : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj middle last)
    (hlastOther : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj last other)
    (hotherFirst : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj other first)
    (hfirstLast : first ≠ last) (hmiddleOther : middle ≠ other) :
    (dualFourCycleWalk graphData hfirstMiddle hmiddleLast hlastOther
      hotherFirst).IsCycle := by
  simp [dualFourCycleWalk, SimpleGraph.Walk.isCycle_def,
    SimpleGraph.Walk.isTrail_def, hfirstMiddle.ne,
    hfirstMiddle.ne.symm, hmiddleLast.ne,
    hlastOther.ne, hotherFirst.ne,
    hotherFirst.ne.symm, hfirstLast, hfirstLast.symm,
    hmiddleOther]

/-- **L1 (closed two-step collision classification).** An extra common
neighbour of a nonadjacent facial-dual endpoint pair at distance two is
adjacent to the displayed middle face. -/
theorem middle_adj_other_of_two_common_neighbors
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {first middle last other : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (hfirstMiddle : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj first middle)
    (hmiddleLast : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj middle last)
    (hfirstOther : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj first other)
    (hotherLast : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj other last)
    (hnotFirstLast : ¬ (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj first last)
    (hfirstNeLast : first ≠ last)
    (hotherNeMiddle : other ≠ middle) :
    (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj middle other := by
  let walk := dualFourCycleWalk graphData hfirstMiddle hmiddleLast
    hotherLast.symm hfirstOther.symm
  have hcycle : walk.IsCycle := by
    exact dualFourCycleWalk_isCycle graphData hfirstMiddle hmiddleLast
      hotherLast.symm hfirstOther.symm hfirstNeLast hotherNeMiddle.symm
  have hregular : G.IsRegularOfDegree 3 :=
    graphData.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hcyclic : CyclicallyFiveEdgeConnected G :=
    GoertzelV24FourEdgeCutGluing.cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample
      graphData minimal
  have hdelete :
      ¬ (G.deleteEdges
        (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
          (pairwiseUniqueSharedInteriorEdges graphData minimal) walk)).Connected := by
    exact
      GoertzelV24DualCycleSeparator.not_connected_deleteEdges_dualWalkPrimalCut_of_isCycle
        graphData minimal.facesTwoSided
        (orbitFaceInteriorDual_connected graphData.toRotationSystem
          minimal.spherical.cubic minimal.primalConnected
          minimal.vertexRotationCyclic)
        hconnected minimal.spherical
        (pairwiseUniqueSharedInteriorEdges graphData minimal) walk hcycle
  rcases
      GoertzelV24DualCycleSeparator.exists_primalCut_adjacent_pair_collar_with_opposite_walk_chord_of_isCycle_of_length_eq_four
        graphData hregular hconnected hcyclic minimal.vertexRotationCyclic
        minimal.facesTwoSided
        (pairwiseUniqueSharedInteriorEdges graphData minimal) walk hcycle
        (by simp [walk]) hdelete with
    ⟨_component, _insideFirst, _insideSecond, _hneInside, _hsupp,
      _hadjInside, _hboundary, _hfirstBoundary, _hsecondBoundary,
      _internalEdge, leftFace, rightFace, step, _hinternalEdge,
      _hinternalNotRemoved, _hleftBoundary, _hrightBoundary, hchord,
      hleftPosition, hrightPosition⟩
  rcases (SimpleGraph.Walk.isChord_sym2Mk.1 hchord) with
    ⟨hleftRight, _hnotEdge, _hleftSupport, _hrightSupport⟩
  have hstepLt : step.val < 4 := by
    simpa [walk] using step.isLt
  have hrotateTwice :
      (finRotate walk.length (finRotate walk.length step)).val =
        (step.val + 2) % 4 := by
    simp only [finRotate_apply, Fin.val_add, Fin.val_one']
    simp [walk]
  interval_cases hstep : step.val
  · have hleft : leftFace = first := by
      simpa [walk, dualFourCycleWalk, hstep] using hleftPosition.symm
    have hright : rightFace = last := by
      rw [hrotateTwice] at hrightPosition
      simpa [walk, dualFourCycleWalk, hstep] using hrightPosition.symm
    exact (hnotFirstLast (hleft ▸ hright ▸ hleftRight)).elim
  · have hleft : leftFace = middle := by
      simpa [walk, dualFourCycleWalk, hstep] using hleftPosition.symm
    have hright : rightFace = other := by
      rw [hrotateTwice] at hrightPosition
      simpa [walk, dualFourCycleWalk, hstep] using hrightPosition.symm
    simpa [hleft, hright] using hleftRight
  · have hleft : leftFace = last := by
      simpa [walk, dualFourCycleWalk, hstep] using hleftPosition.symm
    have hright : rightFace = first := by
      rw [hrotateTwice] at hrightPosition
      simpa [walk, dualFourCycleWalk, hstep] using hrightPosition.symm
    exact (hnotFirstLast (hleft ▸ hright ▸ hleftRight.symm)).elim
  · have hleft : leftFace = other := by
      simpa [walk, dualFourCycleWalk, hstep] using hleftPosition.symm
    have hright : rightFace = middle := by
      rw [hrotateTwice] at hrightPosition
      simpa [walk, dualFourCycleWalk, hstep] using hrightPosition.symm
    simpa [hleft, hright] using hleftRight.symm

/-- **L1 (closed corridor specialization).** In an induced facial-dual
corridor, every common neighbour of the faces two steps apart is adjacent to
the displayed middle face.  Geodesicity supplies the missing diagonal and
injectivity supplies distinctness; the four-cycle classification above does
the remaining planar work. -/
theorem OrbitHexCorridorSkeleton.middle_adj_commonNeighbor_of_two_step
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton graphData.toRotationSystem
      corridorLength)
    {first middle last : Fin corridorLength}
    (hmiddle : middle.val = first.val + 1)
    (hlast : last.val = middle.val + 1)
    (other : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem)))
    (hfirstOther : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj
          (corridor.faceAt first) other)
    (hotherLast : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj
          other (corridor.faceAt last))
    (hotherNeMiddle : other ≠ corridor.faceAt middle) :
    (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj
        (corridor.faceAt middle) other := by
  have hfirstMiddle := corridor.consecutive_adjacent first middle hmiddle
  have hmiddleLast := corridor.consecutive_adjacent middle last hlast
  have hseparated : first.val + 1 < last.val := by omega
  have hnotFirstLast := corridor.separated_not_adjacent first last hseparated
  have hfirstNeLast : corridor.faceAt first ≠ corridor.faceAt last := by
    apply corridor.faceAt_ne
    intro hindices
    have hvalues := congrArg Fin.val hindices
    omega
  exact middle_adj_other_of_two_common_neighbors graphData minimal
    hfirstMiddle hmiddleLast hfirstOther hotherLast hnotFirstLast
    hfirstNeLast hotherNeMiddle

end

end GoertzelV24MinimalDualFourCycleClassification

end Mettapedia.GraphTheory.FourColor
