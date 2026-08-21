import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareSourceRungIncidence
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareEndpointTriangles

/-!
# L1: allocate both source rungs to the square-bond endpoints

The canonical first--third replacement square retains its two consecutive
centre-to-centre source rungs as literal selected crossings.  The exact
two-vertex residue meets each rung, so there are only four endpoint
allocations: both rungs meet the first endpoint, both meet the second, or the
two possible split orientations.

This is the finite allocation packet needed before comparing the pointed
rail crossings with the square component.  It does not identify either
pointed crossing with the square packet, choose a bypass, iterate a rail
repair, attach end caps, construct separated crosscuts, or close Fable flag
L1.
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

/-- Reselecting the second square step leaves the literal first source-rung
anchor unchanged. -/
@[simp] theorem squareDualCycleWithSecondRung_anchorEdge
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
    (squareDualCycleWithSecondRung (rungs := rungs)
      hfirst hthird hfaceSecond).cycle.anchorEdge =
        rungs.edge firstInterior.outgoing := by
  rfl

/-- The four possible incidences of the two consecutive source rungs with
the two vertices of the exact square bond.  Constructor names retain the
orientation instead of collapsing the split case to an unordered statement. -/
inductive SquareBondRealization.SourceRungEndpointAllocation
    {face : SelectedFace (web := web)}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (firstRung secondRung : G.edgeSet) : Prop
  | sameFirst
      (firstRung_mem : bond.first ∈ firstRung.1)
      (secondRung_mem : bond.first ∈ secondRung.1)
  | sameSecond
      (firstRung_mem : bond.second ∈ firstRung.1)
      (secondRung_mem : bond.second ∈ secondRung.1)
  | firstThenSecond
      (firstRung_mem : bond.first ∈ firstRung.1)
      (secondRung_mem : bond.second ∈ secondRung.1)
  | secondThenFirst
      (firstRung_mem : bond.second ∈ firstRung.1)
      (secondRung_mem : bond.first ∈ secondRung.1)

/-- The same four source-rung allocations expressed in the selected crossing
sets of the two endpoint triangles. -/
inductive SquareBondRealization.SourceRungTriangleAllocation
    {face : SelectedFace (web := web)}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    (firstTriangle secondTriangle : bond.EndpointSelectedTriangle)
    (firstRung secondRung : G.edgeSet) : Prop
  | bothFirst
      (firstRung_mem : firstRung ∈ firstTriangle.selectedCycle.crossingEdges)
      (secondRung_mem : secondRung ∈ firstTriangle.selectedCycle.crossingEdges)
  | bothSecond
      (firstRung_mem : firstRung ∈ secondTriangle.selectedCycle.crossingEdges)
      (secondRung_mem : secondRung ∈ secondTriangle.selectedCycle.crossingEdges)
  | firstThenSecond
      (firstRung_mem : firstRung ∈ firstTriangle.selectedCycle.crossingEdges)
      (secondRung_mem : secondRung ∈ secondTriangle.selectedCycle.crossingEdges)
  | secondThenFirst
      (firstRung_mem : firstRung ∈ secondTriangle.selectedCycle.crossingEdges)
      (secondRung_mem : secondRung ∈ firstTriangle.selectedCycle.crossingEdges)

/-- Transport an endpoint allocation into the two exact endpoint triangles.
This is only incidence normalization: the triangles themselves are still the
literal objects constructed from the square bond. -/
theorem SquareBondRealization.SourceRungEndpointAllocation.toTriangleAllocation
    {face : SelectedFace (web := web)}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    {firstRung secondRung : G.edgeSet}
    (allocation : bond.SourceRungEndpointAllocation firstRung secondRung)
    (firstTriangle secondTriangle : bond.EndpointSelectedTriangle)
    (hfirstCenter : firstTriangle.center = bond.first)
    (hsecondCenter : secondTriangle.center = bond.second) :
    bond.SourceRungTriangleAllocation firstTriangle secondTriangle
      firstRung secondRung := by
  have mem_firstTriangle {edge : G.edgeSet}
      (hmem : bond.first ∈ edge.1) :
      edge ∈ firstTriangle.selectedCycle.crossingEdges := by
    rw [firstTriangle.crossingEdges_eq_incidentEdgeFinset, hfirstCenter]
    simpa [incidentEdgeFinset] using hmem
  have mem_secondTriangle {edge : G.edgeSet}
      (hmem : bond.second ∈ edge.1) :
      edge ∈ secondTriangle.selectedCycle.crossingEdges := by
    rw [secondTriangle.crossingEdges_eq_incidentEdgeFinset, hsecondCenter]
    simpa [incidentEdgeFinset] using hmem
  cases allocation with
  | sameFirst hfirst hsecond =>
      exact .bothFirst (mem_firstTriangle hfirst) (mem_firstTriangle hsecond)
  | sameSecond hfirst hsecond =>
      exact .bothSecond (mem_secondTriangle hfirst)
        (mem_secondTriangle hsecond)
  | firstThenSecond hfirst hsecond =>
      exact .firstThenSecond (mem_firstTriangle hfirst)
        (mem_secondTriangle hsecond)
  | secondThenFirst hfirst hsecond =>
      exact .secondThenFirst (mem_secondTriangle hfirst)
        (mem_firstTriangle hsecond)

/-- **L1 exact source-rung allocation.**  Both selected source rungs are
allocated simultaneously to the two vertices of the literal square bond.
No endpoint orientation or same-endpoint hypothesis is added. -/
theorem SquareBondRealization.sourceRungEndpointAllocation
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
    bond.SourceRungEndpointAllocation
      (rungs.edge firstInterior.outgoing)
      (rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing) := by
  have hfirstRung :
      bond.first ∈ (rungs.edge firstInterior.outgoing).1 ∨
        bond.second ∈ (rungs.edge firstInterior.outgoing).1 := by
    have hanchor := bond.anchorEdge_meets_endpoint
    rw [squareDualCycleWithSecondRung_anchorEdge
      (rungs := rungs) hfirst hthird hfaceSecond] at hanchor
    exact hanchor
  have hsecondRung :
      bond.first ∈
          (rungs.edge
            (nextCorridorInterior firstInterior hfirstNext).outgoing).1 ∨
        bond.second ∈
          (rungs.edge
            (nextCorridorInterior firstInterior hfirstNext).outgoing).1 :=
    bond.secondRung_meets_endpoint hfirst hthird hfaceSecond
  rcases hfirstRung with hfirstAtFirst | hfirstAtSecond
  · rcases hsecondRung with hsecondAtFirst | hsecondAtSecond
    · exact .sameFirst hfirstAtFirst hsecondAtFirst
    · exact .firstThenSecond hfirstAtFirst hsecondAtSecond
  · rcases hsecondRung with hsecondAtFirst | hsecondAtSecond
    · exact .secondThenFirst hfirstAtSecond hsecondAtFirst
    · exact .sameSecond hfirstAtSecond hsecondAtSecond

/-- Construct the exact endpoint-triangle decomposition together with the
four-way allocation of the two literal source rungs.  The packet also retains
the exact intersection and union of the two triangle crossing sets. -/
theorem SquareBondRealization.exists_endpointSelectedTriangles_exact_with_sourceRungAllocation
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
        hfirst hthird hfaceSecond).cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    ∃ firstTriangle secondTriangle : bond.EndpointSelectedTriangle,
      firstTriangle.center = bond.first ∧
        secondTriangle.center = bond.second ∧
        firstTriangle.selectedCycle.crossingEdges ∩
            secondTriangle.selectedCycle.crossingEdges = {bond.internalEdge} ∧
        firstTriangle.selectedCycle.crossingEdges ∪
            secondTriangle.selectedCycle.crossingEdges =
          insert bond.internalEdge
            (squareDualCycleWithSecondRung (rungs := rungs)
              hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdges ∧
        bond.SourceRungTriangleAllocation firstTriangle secondTriangle
          (rungs.edge firstInterior.outgoing)
          (rungs.edge
            (nextCorridorInterior firstInterior hfirstNext).outgoing) := by
  rcases bond.exists_endpointSelectedTriangles_exact hroot with
    ⟨firstTriangle, secondTriangle, hfirstCenter, hsecondCenter,
      hinter, hunion⟩
  let allocation := bond.sourceRungEndpointAllocation
    hfirst hthird hfaceSecond
  exact ⟨firstTriangle, secondTriangle, hfirstCenter, hsecondCenter,
    hinter, hunion,
    allocation.toTriangleAllocation firstTriangle secondTriangle
      hfirstCenter hsecondCenter⟩

end MiddleReplacementShortDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
