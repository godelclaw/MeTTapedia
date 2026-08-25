import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareSourceRungRemainder

/-!
# L1: identify the two non-rung sides of the literal source square

The canonical first--third replacement square is ordered as first centre,
second centre, third centre, collision face.  Its first two selected primal
crossings are the two consecutive source rungs.  This module proves that the
two crossings left after deleting those rungs are exactly the crossings at
the third-centre--collision and collision--first-centre sides.

This is the exact finite target for the pointed-edge comparison.  It does not
identify either actual pointed rail crossing with one of these two sides,
place a pointed corner in the square component, choose or splice a bypass,
iterate a rail repair, attach end caps, construct separated crosscuts, or
close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

private abbrev SelectedFace
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

namespace MiddleReplacementShortDualCycle

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}

/-- Step `2` of a literal source square. -/
def squareThirdStep
    {face : SelectedFace web}
    (square : MiddleReplacementSquareDualCycle (web := web) face) :
    Fin square.cycle.walk.length :=
  ⟨2, by rw [square.length_eq_four]; omega⟩

/-- Step `3` of a literal source square. -/
def squareFourthStep
    {face : SelectedFace web}
    (square : MiddleReplacementSquareDualCycle (web := web) face) :
    Fin square.cycle.walk.length :=
  ⟨3, by rw [square.length_eq_four]; omega⟩

@[simp] theorem squareThirdStep_val
    {face : SelectedFace web}
    (square : MiddleReplacementSquareDualCycle (web := web) face) :
    (squareThirdStep square).val = 2 := rfl

@[simp] theorem squareFourthStep_val
    {face : SelectedFace web}
    (square : MiddleReplacementSquareDualCycle (web := web) face) :
    (squareFourthStep square).val = 3 := rfl

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

/-- The two non-rung selected crossings are precisely the two sides incident
with the collision face in the ordered first--third square. -/
theorem sourceRungRemainder_eq_collisionSideCrossings
    {face : SelectedFace web}
    (hfirst : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          firstInterior.center) face)
    (hthird : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
        face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    sourceRungRemainder (rungs := rungs) hfirst hthird hfaceSecond =
      { (squareDualCycleWithSecondRung (rungs := rungs)
            hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdge
          (squareThirdStep (squareDualCycleWithSecondRung (rungs := rungs)
            hfirst hthird hfaceSecond)),
        (squareDualCycleWithSecondRung (rungs := rungs)
            hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdge
          (squareFourthStep (squareDualCycleWithSecondRung (rungs := rungs)
            hfirst hthird hfaceSecond)) } := by
  let square := squareDualCycleWithSecondRung (rungs := rungs)
    hfirst hthird hfaceSecond
  let secondStep := squareSecondStep
    (squareDualCycle_of_firstThirdSquare (rungs := rungs)
      hfirst hthird hfaceSecond)
  let thirdStep := squareThirdStep square
  let fourthStep := squareFourthStep square
  let thirdEdge := square.cycle.selectedCycle.crossingEdge thirdStep
  let fourthEdge := square.cycle.selectedCycle.crossingEdge fourthStep
  have hinjective := square.cycle.selectedCycle.crossingEdge_injective
    (orbitFace_incidence_le_two web.annular.RS)
  have hfirstEdge : square.cycle.selectedCycle.crossingEdge
      square.cycle.anchor = rungs.edge firstInterior.outgoing := by
    simp [square]
  have hsecondEdge : square.cycle.selectedCycle.crossingEdge secondStep =
      rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing := by
    change square.cycle.crossingEdge secondStep = _
    simp [square, secondStep]
  have hthird_ne_anchor : thirdStep ≠ square.cycle.anchor := by
    intro h
    have hval := congrArg Fin.val h
    have hanchor : square.cycle.anchor.val = 0 := rfl
    simp [thirdStep] at hval
    omega
  have hthird_ne_second : thirdStep ≠ secondStep := by
    intro h
    have hval := congrArg Fin.val h
    simp [thirdStep, secondStep] at hval
  have hfourth_ne_anchor : fourthStep ≠ square.cycle.anchor := by
    intro h
    have hval := congrArg Fin.val h
    have hanchor : square.cycle.anchor.val = 0 := rfl
    simp [fourthStep] at hval
    omega
  have hfourth_ne_second : fourthStep ≠ secondStep := by
    intro h
    have hval := congrArg Fin.val h
    simp [fourthStep, secondStep] at hval
  have hthird_ne_fourth : thirdStep ≠ fourthStep := by
    intro h
    have hval := congrArg Fin.val h
    simp [thirdStep, fourthStep] at hval
  have hthirdEdge_ne_first : thirdEdge ≠ rungs.edge firstInterior.outgoing := by
    intro h
    apply hthird_ne_anchor
    apply hinjective
    exact h.trans hfirstEdge.symm
  have hthirdEdge_ne_second : thirdEdge ≠
      rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing := by
    intro h
    apply hthird_ne_second
    apply hinjective
    exact h.trans hsecondEdge.symm
  have hfourthEdge_ne_first : fourthEdge ≠ rungs.edge firstInterior.outgoing := by
    intro h
    apply hfourth_ne_anchor
    apply hinjective
    exact h.trans hfirstEdge.symm
  have hfourthEdge_ne_second : fourthEdge ≠
      rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing := by
    intro h
    apply hfourth_ne_second
    apply hinjective
    exact h.trans hsecondEdge.symm
  have hthird_mem : thirdEdge ∈ sourceRungRemainder (rungs := rungs)
      hfirst hthird hfaceSecond := by
    rw [sourceRungRemainder]
    apply Finset.mem_erase.2
    refine ⟨hthirdEdge_ne_second, Finset.mem_erase.2
      ⟨hthirdEdge_ne_first, ?_⟩⟩
    exact (square.cycle.selectedCycle.mem_crossingEdges_iff _).2
      ⟨thirdStep, rfl⟩
  have hfourth_mem : fourthEdge ∈ sourceRungRemainder (rungs := rungs)
      hfirst hthird hfaceSecond := by
    rw [sourceRungRemainder]
    apply Finset.mem_erase.2
    refine ⟨hfourthEdge_ne_second, Finset.mem_erase.2
      ⟨hfourthEdge_ne_first, ?_⟩⟩
    exact (square.cycle.selectedCycle.mem_crossingEdges_iff _).2
      ⟨fourthStep, rfl⟩
  have hedges_ne : thirdEdge ≠ fourthEdge := by
    intro h
    exact hthird_ne_fourth (hinjective h)
  have hpair_subset : ({thirdEdge, fourthEdge} : Finset G.edgeSet) ⊆
      sourceRungRemainder (rungs := rungs) hfirst hthird hfaceSecond := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · exact hthird_mem
    · exact hfourth_mem
  have hcard_le :
      (sourceRungRemainder (rungs := rungs) hfirst hthird hfaceSecond).card ≤
        ({thirdEdge, fourthEdge} : Finset G.edgeSet).card := by
    rw [sourceRungRemainder_card_eq_two (rungs := rungs)
      hfirst hthird hfaceSecond]
    simp [hedges_ne]
  exact (Finset.eq_of_subset_of_card_le hpair_subset hcard_le).symm

end MiddleReplacementShortDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
