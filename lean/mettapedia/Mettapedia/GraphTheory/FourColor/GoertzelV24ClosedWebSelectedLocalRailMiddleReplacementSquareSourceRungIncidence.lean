import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementCrossingSelection
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareBond

/-!
# L1: the two literal source rungs meet the replacement-square bond

The canonical first--third replacement square now retains both consecutive
centre-to-centre source rungs as selected primal crossings.  In the acyclic
square residue, the exact two-vertex bond therefore meets each rung.

This is the graph-level incidence supplied by the selected separator.  It
does not identify which endpoint each rung meets, place either pointed rail
corner in the component, construct the local bypass, iterate the rail repair,
attach end caps, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
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

/-- The literal second centre-to-centre rung meets one endpoint of the exact
two-vertex bond carried by the reselected first--third square. -/
theorem SquareBondRealization.secondRung_meets_endpoint
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
        (nextCorridorInterior firstInterior hfirstNext).center)
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        (squareDualCycleWithSecondRung (rungs := rungs)
          hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdges)
        ).ConnectedComponent}
    (bond : SquareBondRealization
      (squareDualCycleWithSecondRung (rungs := rungs)
        hfirst hthird hfaceSecond).cycle component) :
    bond.first ∈
        (rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing).1 ∨
      bond.second ∈
        (rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing).1 := by
  let square := squareDualCycleWithSecondRung (rungs := rungs)
    hfirst hthird hfaceSecond
  apply bond.covers_crossingEdges
  apply (square.cycle.selectedCycle.mem_crossingEdges_iff _).2
  refine ⟨squareSecondStep
    (squareDualCycle_of_firstThirdSquare (rungs := rungs)
      hfirst hthird hfaceSecond), ?_⟩
  exact squareDualCycleWithSecondRung_crossingEdge_secondStep
    (rungs := rungs) hfirst hthird hfaceSecond

end MiddleReplacementShortDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
