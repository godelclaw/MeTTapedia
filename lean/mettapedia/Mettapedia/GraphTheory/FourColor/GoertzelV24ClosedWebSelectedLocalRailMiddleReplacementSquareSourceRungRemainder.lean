import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareSourceRungAllocation

/-!
# L1: remove the two literal source rungs from the square boundary

The canonical first--third replacement square has four distinct selected
primal crossings.  Two of them are now literal source rungs: the outgoing
rungs of the first and second Cell--3 interiors.  This module records their
distinctness and proves that deleting them leaves exactly two selected
crossings.

Those two remaining crossings are the finite target for the pointed-edge
comparison.  This file does not identify them with the two actual pointed
rail crossings, place either pointed corner in the square component, choose
a bypass, iterate a rail repair, attach end caps, construct separated
crosscuts, or close Fable flag L1.
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
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

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

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

namespace MiddleReplacementShortDualCycle

/-- Delete the two literal centre-to-centre source rungs from the selected
four-edge square boundary. -/
def sourceRungRemainder
    {face : SelectedFace (web := web)}
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
    Finset G.edgeSet :=
  (((squareDualCycleWithSecondRung (rungs := rungs)
      hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdges.erase
        (rungs.edge firstInterior.outgoing)).erase
      (rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing))

/-- The first and second literal source rungs are distinct.  The proof reads
them at two different steps of the same selected simple dual square. -/
theorem sourceRungs_ne
    {face : SelectedFace (web := web)}
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
    rungs.edge firstInterior.outgoing ≠
      rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing := by
  let square := squareDualCycleWithSecondRung (rungs := rungs)
    hfirst hthird hfaceSecond
  let secondStep := squareSecondStep
    (squareDualCycle_of_firstThirdSquare (rungs := rungs)
      hfirst hthird hfaceSecond)
  have hstep : secondStep ≠ square.cycle.anchor := by
    intro heq
    have hval := congrArg Fin.val heq
    have hanchor : square.cycle.anchor.val = 0 := rfl
    have hsecond : secondStep.val = 1 := rfl
    omega
  have hfirstEdge : square.cycle.selectedCycle.crossingEdge
      square.cycle.anchor = rungs.edge firstInterior.outgoing := by
    simp [square]
  have hsecondEdge : square.cycle.selectedCycle.crossingEdge secondStep =
      rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing := by
    change square.cycle.crossingEdge secondStep = _
    simp [square, secondStep]
  have hinjective := square.cycle.selectedCycle.crossingEdge_injective
    (orbitFace_incidence_le_two web.annular.RS)
  intro hedges
  apply hstep
  apply hinjective
  exact hsecondEdge.trans (hedges.symm.trans hfirstEdge.symm)

/-- Both literal source rungs belong to the selected square boundary. -/
theorem sourceRungs_mem_crossingEdges
    {face : SelectedFace (web := web)}
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
    rungs.edge firstInterior.outgoing ∈
        (squareDualCycleWithSecondRung (rungs := rungs)
          hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdges ∧
      rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing ∈
        (squareDualCycleWithSecondRung (rungs := rungs)
          hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdges := by
  let square := squareDualCycleWithSecondRung (rungs := rungs)
    hfirst hthird hfaceSecond
  let secondStep := squareSecondStep
    (squareDualCycle_of_firstThirdSquare (rungs := rungs)
      hfirst hthird hfaceSecond)
  have hsecondEdge : square.cycle.selectedCycle.crossingEdge secondStep =
      rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing := by
    change square.cycle.crossingEdge secondStep = _
    simp [square, secondStep]
  constructor
  · apply (square.cycle.selectedCycle.mem_crossingEdges_iff _).2
    refine ⟨square.cycle.anchor, ?_⟩
    simp [square]
  · apply (square.cycle.selectedCycle.mem_crossingEdges_iff _).2
    exact ⟨secondStep, hsecondEdge⟩

/-- Exactly two selected square crossings remain after deleting the two
literal source rungs. -/
theorem sourceRungRemainder_card_eq_two
    {face : SelectedFace (web := web)}
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
    (sourceRungRemainder (rungs := rungs)
      hfirst hthird hfaceSecond).card = 2 := by
  let square := squareDualCycleWithSecondRung (rungs := rungs)
    hfirst hthird hfaceSecond
  have hcard : square.cycle.selectedCycle.crossingEdges.card = 4 := by
    rw [square.cycle.crossingEdges_card_eq_length]
    exact square.length_eq_four
  have hrungs := sourceRungs_mem_crossingEdges
    (rungs := rungs) hfirst hthird hfaceSecond
  have hne := sourceRungs_ne (rungs := rungs)
    hfirst hthird hfaceSecond
  have hsecondAfterFirst :
      rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing ∈
        square.cycle.selectedCycle.crossingEdges.erase
          (rungs.edge firstInterior.outgoing) := by
    exact Finset.mem_erase.2 ⟨hne.symm, hrungs.2⟩
  rw [sourceRungRemainder, Finset.card_erase_of_mem hsecondAfterFirst,
    Finset.card_erase_of_mem hrungs.1, hcard]

end MiddleReplacementShortDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
