import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareCornerResolution

/-!
# L1: resolve the third edge at a square-packet corner

Two distinct square-packet edges meeting one source corner determine whether
that corner is a bond endpoint or an exterior two-arm fan.  A third distinct
edge at the same corner therefore has an exact dichotomy.  At a bond endpoint
it meets the selected two-vertex residue.  At an exterior corner it meets
neither endpoint: otherwise simplicity would identify it with one of the two
already named arms.

The theorem keeps both exterior orientations and both avoidance proofs.  It
does not identify an actual pointed rail crossing with this third edge,
construct a replacement, prove companion separation, iterate a rolling
repair, attach end caps, or close Fable flag L1.
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

/-- Exact fate of a third distinct edge at a corner shared by two allocated
square-packet edges.  The exterior constructors retain the arm equations
and prove that the third edge avoids both bond endpoints. -/
inductive SquareBondRealization.BoundaryPairThirdEdgeResolution
    {face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (firstEdge secondEdge thirdEdge : G.edgeSet) (corner : V) : Prop
  | atFirst
      (corner_eq : corner = bond.first)
      (third_mem : bond.first ∈ thirdEdge.1)
  | atSecond
      (corner_eq : corner = bond.second)
      (third_mem : bond.second ∈ thirdEdge.1)
  | exteriorFirstSecond
      (corner_ne_first : corner ≠ bond.first)
      (corner_ne_second : corner ≠ bond.second)
      (firstEdge_eq : firstEdge.1 = s(corner, bond.first))
      (secondEdge_eq : secondEdge.1 = s(corner, bond.second))
      (third_not_first : bond.first ∉ thirdEdge.1)
      (third_not_second : bond.second ∉ thirdEdge.1)
  | exteriorSecondFirst
      (corner_ne_first : corner ≠ bond.first)
      (corner_ne_second : corner ≠ bond.second)
      (firstEdge_eq : firstEdge.1 = s(corner, bond.second))
      (secondEdge_eq : secondEdge.1 = s(corner, bond.first))
      (third_not_first : bond.first ∉ thirdEdge.1)
      (third_not_second : bond.second ∉ thirdEdge.1)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem endpoint_not_mem_third_of_arm
    {arm third : G.edgeSet} {corner endpoint : V}
    (hcornerEndpoint : corner ≠ endpoint)
    (harm : arm.1 = s(corner, endpoint))
    (hthirdNe : third ≠ arm)
    (hcornerThird : corner ∈ third.1) :
    endpoint ∉ third.1 := by
  intro hendpointThird
  have hthird : third.1 = s(corner, endpoint) :=
    (Sym2.mem_and_mem_iff hcornerEndpoint).1
      ⟨hcornerThird, hendpointThird⟩
  apply hthirdNe
  exact Subtype.ext (hthird.trans harm.symm)

/-- A third distinct edge at the common corner either meets the component at
that endpoint or is proved disjoint from both component vertices. -/
theorem SquareBondRealization.BoundaryPairCommonCornerResolution.thirdEdgeResolution
    {face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    {firstEdge secondEdge thirdEdge : G.edgeSet} {corner : V}
    (resolution : bond.BoundaryPairCommonCornerResolution
      firstEdge secondEdge corner)
    (hthirdFirst : thirdEdge ≠ firstEdge)
    (hthirdSecond : thirdEdge ≠ secondEdge)
    (hcornerThird : corner ∈ thirdEdge.1) :
    bond.BoundaryPairThirdEdgeResolution
      firstEdge secondEdge thirdEdge corner := by
  cases resolution with
  | atFirst hcorner =>
      exact .atFirst hcorner (hcorner ▸ hcornerThird)
  | atSecond hcorner =>
      exact .atSecond hcorner (hcorner ▸ hcornerThird)
  | exteriorFirstSecond hfirst hsecond hfirstEdge hsecondEdge =>
      exact .exteriorFirstSecond hfirst hsecond hfirstEdge hsecondEdge
        (endpoint_not_mem_third_of_arm hfirst hfirstEdge hthirdFirst hcornerThird)
        (endpoint_not_mem_third_of_arm hsecond hsecondEdge hthirdSecond hcornerThird)
  | exteriorSecondFirst hfirst hsecond hfirstEdge hsecondEdge =>
      exact .exteriorSecondFirst hfirst hsecond hfirstEdge hsecondEdge
        (endpoint_not_mem_third_of_arm hfirst hsecondEdge hthirdSecond hcornerThird)
        (endpoint_not_mem_third_of_arm hsecond hfirstEdge hthirdFirst hcornerThird)

/-- Specialize the third-edge dichotomy to the two source rungs. -/
theorem SquareBondRealization.SourceAndCollisionEndpointAllocation.sourceRungThirdEdgeResolution
    {face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    {firstRung secondRung thirdSide fourthSide thirdEdge : G.edgeSet}
    (allocation : bond.SourceAndCollisionEndpointAllocation
      firstRung secondRung thirdSide fourthSide)
    (corner : V) (hrungs : firstRung ≠ secondRung)
    (hcornerFirst : corner ∈ firstRung.1)
    (hcornerSecond : corner ∈ secondRung.1)
    (hthirdFirst : thirdEdge ≠ firstRung)
    (hthirdSecond : thirdEdge ≠ secondRung)
    (hcornerThird : corner ∈ thirdEdge.1) :
    bond.BoundaryPairThirdEdgeResolution
      firstRung secondRung thirdEdge corner := by
  exact (allocation.sourceRungCornerResolution corner hrungs
    hcornerFirst hcornerSecond).thirdEdgeResolution
      hthirdFirst hthirdSecond hcornerThird

/-- Specialize the same dichotomy to the two collision-adjacent sides. -/
theorem SquareBondRealization.SourceAndCollisionEndpointAllocation.collisionSideThirdEdgeResolution
    {face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : SquareBondRealization cycle component}
    {firstRung secondRung thirdSide fourthSide thirdEdge : G.edgeSet}
    (allocation : bond.SourceAndCollisionEndpointAllocation
      firstRung secondRung thirdSide fourthSide)
    (corner : V) (hsides : thirdSide ≠ fourthSide)
    (hcornerThirdSide : corner ∈ thirdSide.1)
    (hcornerFourthSide : corner ∈ fourthSide.1)
    (hthirdThirdSide : thirdEdge ≠ thirdSide)
    (hthirdFourthSide : thirdEdge ≠ fourthSide)
    (hcornerThird : corner ∈ thirdEdge.1) :
    bond.BoundaryPairThirdEdgeResolution
      thirdSide fourthSide thirdEdge corner := by
  exact (allocation.collisionSideCornerResolution corner hsides
    hcornerThirdSide hcornerFourthSide).thirdEdgeResolution
      hthirdThirdSide hthirdFourthSide hcornerThird

end MiddleReplacementShortDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
