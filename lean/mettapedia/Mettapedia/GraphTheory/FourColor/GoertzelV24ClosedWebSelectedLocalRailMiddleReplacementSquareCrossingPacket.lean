import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareCollisionSideCrossings

/-!
# L1: enumerate the literal source-square crossing packet

The canonical first--third replacement square has four selected primal
crossings.  Two are the consecutive centre-to-centre source rungs; the other
two are the collision-adjacent sides identified by the preceding module.
This file assembles those facts into one exact four-edge equality.

This is the finite target for the pointed-edge comparison.  It does not
classify an actual pointed crossing into the packet, place a pointed corner
in the square component, construct or splice a bypass, iterate a rail repair,
attach end caps, construct separated crosscuts, or close Fable flag L1.
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

/-- **L1 exact source-square crossing packet.**  The selected crossing set of
the ordered first--third square consists of its two literal source rungs and
its two collision-adjacent sides, with no unnamed remainder. -/
theorem crossingEdges_eq_sourceRungs_insert_collisionSideCrossings
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
    let square := squareDualCycleWithSecondRung (rungs := rungs)
      hfirst hthird hfaceSecond
    square.cycle.selectedCycle.crossingEdges =
      { rungs.edge firstInterior.outgoing,
        rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing,
        square.cycle.selectedCycle.crossingEdge (squareThirdStep square),
        square.cycle.selectedCycle.crossingEdge (squareFourthStep square) } := by
  classical
  dsimp only
  let square := squareDualCycleWithSecondRung (rungs := rungs)
    hfirst hthird hfaceSecond
  let firstRung := rungs.edge firstInterior.outgoing
  let secondRung :=
    rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing
  let thirdEdge :=
    square.cycle.selectedCycle.crossingEdge (squareThirdStep square)
  let fourthEdge :=
    square.cycle.selectedCycle.crossingEdge (squareFourthStep square)
  have hrungs := sourceRungs_mem_crossingEdges (rungs := rungs)
    hfirst hthird hfaceSecond
  have hremainder := sourceRungRemainder_eq_collisionSideCrossings
    (rungs := rungs) hfirst hthird hfaceSecond
  change square.cycle.selectedCycle.crossingEdges =
    {firstRung, secondRung, thirdEdge, fourthEdge}
  ext edge
  constructor
  · intro hedge
    by_cases hfirstEdge : edge = firstRung
    · simp [hfirstEdge]
    by_cases hsecondEdge : edge = secondRung
    · simp [hsecondEdge]
    have hrem : edge ∈ sourceRungRemainder (rungs := rungs)
        hfirst hthird hfaceSecond := by
      rw [sourceRungRemainder]
      exact Finset.mem_erase.2
        ⟨hsecondEdge, Finset.mem_erase.2 ⟨hfirstEdge, hedge⟩⟩
    rw [hremainder] at hrem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hrem
    have hcollision : edge = thirdEdge ∨ edge = fourthEdge := by
      simpa only [square, thirdEdge, fourthEdge] using hrem
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inr hcollision)
  · intro hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with hfirstEdge | hsecondEdge | hthirdEdge | hfourthEdge
    · rw [hfirstEdge]
      simpa only [square, firstRung] using hrungs.1
    · rw [hsecondEdge]
      simpa only [square, secondRung] using hrungs.2
    · subst edge
      exact (square.cycle.selectedCycle.mem_crossingEdges_iff thirdEdge).2
        ⟨squareThirdStep square, rfl⟩
    · subst edge
      exact (square.cycle.selectedCycle.mem_crossingEdges_iff fourthEdge).2
        ⟨squareFourthStep square, rfl⟩

end MiddleReplacementShortDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
