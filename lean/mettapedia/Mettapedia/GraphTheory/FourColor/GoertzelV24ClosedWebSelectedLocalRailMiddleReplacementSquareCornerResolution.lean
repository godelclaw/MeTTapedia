import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareEndpointAllocation

/-!
# L1: resolve a common source corner against a square-bond allocation

The exact square packet assigns each of its four selected primal crossings
to one endpoint of the realized two-vertex bond.  A source corner shared by
two distinct packet edges therefore has only three geometric possibilities:
it is the first bond endpoint, it is the second bond endpoint, or the two
edges run from an exterior corner to the two different bond endpoints.

This module proves that elementary simple-graph fact and applies it to both
edge pairs retained by `SourceAndCollisionEndpointAllocation`.  The exterior
case is kept with exact edge equations; it is not discarded as a drawing
artifact.  This is finite source-coordinate data, not yet the classification
of the two pointed rail crossings, a companion-separated repair, rolling
iteration, either end cap, or closure of Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

namespace MiddleReplacementShortDualCycle

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}

/-- Exact resolution of two distinct square-packet edges which meet a common
source corner.  In the exterior alternatives the edge equations retain the
orientation of the two arms; no planar picture is used to choose one. -/
inductive SquareBondRealization.BoundaryPairCommonCornerResolution
    {face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (firstEdge secondEdge : G.edgeSet) (corner : V) : Prop
  | atFirst (corner_eq : corner = bond.first)
  | atSecond (corner_eq : corner = bond.second)
  | exteriorFirstSecond
      (corner_ne_first : corner ≠ bond.first)
      (corner_ne_second : corner ≠ bond.second)
      (firstEdge_eq : firstEdge.1 = s(corner, bond.first))
      (secondEdge_eq : secondEdge.1 = s(corner, bond.second))
  | exteriorSecondFirst
      (corner_ne_first : corner ≠ bond.first)
      (corner_ne_second : corner ≠ bond.second)
      (firstEdge_eq : firstEdge.1 = s(corner, bond.second))
      (secondEdge_eq : secondEdge.1 = s(corner, bond.first))

omit [Fintype V] [DecidableRel G.Adj] in
private theorem commonVertex_eq_of_distinct_edges_meet_same_endpoint
    {firstEdge secondEdge : G.edgeSet} {corner endpoint : V}
    (hedges : firstEdge ≠ secondEdge)
    (hcornerFirst : corner ∈ firstEdge.1)
    (hcornerSecond : corner ∈ secondEdge.1)
    (hendpointFirst : endpoint ∈ firstEdge.1)
    (hendpointSecond : endpoint ∈ secondEdge.1) :
    corner = endpoint := by
  by_contra hcornerEndpoint
  have hfirst : firstEdge.1 = s(corner, endpoint) :=
    (Sym2.mem_and_mem_iff hcornerEndpoint).1
      ⟨hcornerFirst, hendpointFirst⟩
  have hsecond : secondEdge.1 = s(corner, endpoint) :=
    (Sym2.mem_and_mem_iff hcornerEndpoint).1
      ⟨hcornerSecond, hendpointSecond⟩
  apply hedges
  exact Subtype.ext (hfirst.trans hsecond.symm)

/-- Two distinct boundary edges meeting one source corner either identify
that corner with a bond endpoint or exhibit the exact two-arm exterior fan. -/
theorem SquareBondRealization.boundaryPairCommonCornerResolution
    {face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (firstEdge secondEdge : G.edgeSet) (corner : V)
    (hedges : firstEdge ≠ secondEdge)
    (hcornerFirst : corner ∈ firstEdge.1)
    (hcornerSecond : corner ∈ secondEdge.1)
    (hfirstEndpoint : bond.first ∈ firstEdge.1 ∨
      bond.second ∈ firstEdge.1)
    (hsecondEndpoint : bond.first ∈ secondEdge.1 ∨
      bond.second ∈ secondEdge.1) :
    bond.BoundaryPairCommonCornerResolution firstEdge secondEdge corner := by
  rcases hfirstEndpoint with hfirst | hfirst <;>
    rcases hsecondEndpoint with hsecond | hsecond
  · exact .atFirst
      (commonVertex_eq_of_distinct_edges_meet_same_endpoint hedges
        hcornerFirst hcornerSecond hfirst hsecond)
  · by_cases hcornerFirstEndpoint : corner = bond.first
    · exact .atFirst hcornerFirstEndpoint
    · by_cases hcornerSecondEndpoint : corner = bond.second
      · exact .atSecond hcornerSecondEndpoint
      · exact .exteriorFirstSecond hcornerFirstEndpoint
          hcornerSecondEndpoint
          ((Sym2.mem_and_mem_iff hcornerFirstEndpoint).1
            ⟨hcornerFirst, hfirst⟩)
          ((Sym2.mem_and_mem_iff hcornerSecondEndpoint).1
            ⟨hcornerSecond, hsecond⟩)
  · by_cases hcornerFirstEndpoint : corner = bond.first
    · exact .atFirst hcornerFirstEndpoint
    · by_cases hcornerSecondEndpoint : corner = bond.second
      · exact .atSecond hcornerSecondEndpoint
      · exact .exteriorSecondFirst hcornerFirstEndpoint
          hcornerSecondEndpoint
          ((Sym2.mem_and_mem_iff hcornerSecondEndpoint).1
            ⟨hcornerFirst, hfirst⟩)
          ((Sym2.mem_and_mem_iff hcornerFirstEndpoint).1
            ⟨hcornerSecond, hsecond⟩)
  · exact .atSecond
      (commonVertex_eq_of_distinct_edges_meet_same_endpoint hedges
        hcornerFirst hcornerSecond hfirst hsecond)

/-- Apply a six-case square allocation to the two literal source rungs. -/
theorem SquareBondRealization.SourceAndCollisionEndpointAllocation.sourceRungCornerResolution
    {face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    {firstRung secondRung thirdSide fourthSide : G.edgeSet}
    (allocation : bond.SourceAndCollisionEndpointAllocation
      firstRung secondRung thirdSide fourthSide)
    (corner : V) (hedges : firstRung ≠ secondRung)
    (hfirst : corner ∈ firstRung.1)
    (hsecond : corner ∈ secondRung.1) :
    bond.BoundaryPairCommonCornerResolution firstRung secondRung corner := by
  apply bond.boundaryPairCommonCornerResolution firstRung secondRung corner
    hedges hfirst hsecond
  · cases allocation <;> simp_all
  · cases allocation <;> simp_all

/-- Apply the same allocation to the two collision-adjacent square sides. -/
theorem SquareBondRealization.SourceAndCollisionEndpointAllocation.collisionSideCornerResolution
    {face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    {firstRung secondRung thirdSide fourthSide : G.edgeSet}
    (allocation : bond.SourceAndCollisionEndpointAllocation
      firstRung secondRung thirdSide fourthSide)
    (corner : V) (hedges : thirdSide ≠ fourthSide)
    (hthird : corner ∈ thirdSide.1)
    (hfourth : corner ∈ fourthSide.1) :
    bond.BoundaryPairCommonCornerResolution thirdSide fourthSide corner := by
  apply bond.boundaryPairCommonCornerResolution thirdSide fourthSide corner
    hedges hthird hfourth
  · cases allocation <;> simp_all
  · cases allocation <;> simp_all

end MiddleReplacementShortDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
