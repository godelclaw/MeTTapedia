import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppend

/-!
# The exact obstruction to one selected adjacent rail append

The local selected-rail append is constructive when the two consecutive
Cell--3 centres have only the two named flank faces as common neighbours.
Failure of that classification is not left as a negated hypothesis here: it
produces a literal third common neighbour and hence a length-three facial-dual
cycle through the consecutive centres.

This is a fail-closed L1 alternative.  Its left branch is the actual two-cell
rail assembly.  Its right branch is the exact local separator candidate that a
source-local three-edge-cut reduction or a rail rerouting must consume.  The
module proves neither of those later repairs and therefore does not claim the
global corridor or the long end-capped crosscut pair.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

namespace SeparatedSelectedSourceLocalRailSuccessor

variable
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}

/-- Consecutive corridor centres are adjacent in the literal ambient facial
dual graph. -/
private theorem centers_adj : SelectedDualGraph (web := web).Adj
    ((corridor.toCleanOrbitHexCorridorSkeleton
      |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center)
    ((corridor.toCleanOrbitHexCorridorSkeleton
      |>.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior leftInterior hnext).center) := by
  exact (corridor.toCleanOrbitHexCorridorSkeleton
    |>.toOrbitHexCorridorSkeleton).consecutive_adjacent leftInterior.center
      (nextCorridorInterior leftInterior hnext).center rfl

/-- A concrete witness that the exact adjacent common-neighbour
classification fails.  The third face is adjacent to both consecutive
centres but is neither of the two named shared-rung flanks. -/
structure AdjacentDualTriangle
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement) where
  third : SelectedFace (web := web)
  leftCenter_adj_third : SelectedDualGraph (web := web).Adj
    ((corridor.toCleanOrbitHexCorridorSkeleton
      |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center) third
  rightCenter_adj_third : SelectedDualGraph (web := web).Adj
    ((corridor.toCleanOrbitHexCorridorSkeleton
      |>.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior leftInterior hnext).center) third
  third_ne_before :
    third ≠ selectedPlacementSideFace leftPlacement successor.frame.leftBefore
  third_ne_after :
    third ≠ selectedPlacementSideFace leftPlacement successor.frame.leftAfter

namespace AdjacentDualTriangle

variable
    {successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement}

/-- The literal three-step facial-dual walk exposed by an unsuccessful
adjacent append. -/
def walk (triangle : AdjacentDualTriangle successor) :
    SelectedDualGraph (web := web).Walk
      ((corridor.toCleanOrbitHexCorridorSkeleton
        |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center)
      ((corridor.toCleanOrbitHexCorridorSkeleton
        |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center) :=
  .cons (centers_adj (corridor := corridor) (leftInterior := leftInterior)
    (hnext := hnext))
    (.cons triangle.rightCenter_adj_third
      (.cons triangle.leftCenter_adj_third.symm .nil))

@[simp] theorem walk_length (triangle : AdjacentDualTriangle successor) :
    triangle.walk.length = 3 := by
  simp [walk]

/-- The obstruction walk is a genuine dual cycle, not merely a closed walk.
Its three distinct vertices follow directly from the three adjacency
witnesses. -/
theorem walk_isCycle (triangle : AdjacentDualTriangle successor) :
    triangle.walk.IsCycle := by
  have hcenters := centers_adj (corridor := corridor)
    (leftInterior := leftInterior) (hnext := hnext)
  have hleftRight :
      (corridor.toCleanOrbitHexCorridorSkeleton
        |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center ≠
      (corridor.toCleanOrbitHexCorridorSkeleton
        |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.outgoing.right := by
    simpa [nextCorridorInterior] using hcenters.ne
  have hrightThird :
      (corridor.toCleanOrbitHexCorridorSkeleton
        |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.outgoing.right ≠
      triangle.third := by
    simpa [nextCorridorInterior] using triangle.rightCenter_adj_third.ne
  simp [walk, SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def,
    nextCorridorInterior, hleftRight, hleftRight.symm, hrightThird,
    triangle.leftCenter_adj_third.ne,
    triangle.leftCenter_adj_third.ne.symm]

end AdjacentDualTriangle

/-- Failure of `CommonNeighborsExact` produces its positive geometric
witness.  This theorem is the constructive negation used by the append
alternative below. -/
theorem adjacentDualTriangle_of_not_commonNeighborsExact
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (hnot : ¬ successor.CommonNeighborsExact) :
    Nonempty (AdjacentDualTriangle successor) := by
  classical
  simp only [CommonNeighborsExact, not_forall, not_or] at hnot
  rcases hnot with ⟨third, hleft, hright, hbefore, hafter⟩
  exact ⟨⟨third, hleft, hright, hbefore, hafter⟩⟩

end SeparatedSelectedSourceLocalRailSuccessor

namespace SelectedSourceLocalRailAssembly

variable
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {leftIncomingBefore leftIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}

/-- **L1 adjacent append alternative.** Two literal neighbouring selected
Cell--3 rail pairs either construct the append-safe two-cell assembly, or
exhibit the exact length-three facial-dual obstruction to that construction.

The right branch is deliberately positive data.  It is the input expected by
the next source-local separator-reduction or rerouting theorem; this result
does not assume that branch impossible. -/
noncomputable def appendLocalSuccessor_or_adjacentDualTriangle
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) :
    Nonempty (SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter)
      (selectedPlacementSideFace rightPlacement
        successor.rightOutgoingBefore)
      (selectedPlacementSideFace rightPlacement
        successor.rightOutgoingAfter)) ∨
      Nonempty
        (SeparatedSelectedSourceLocalRailSuccessor.AdjacentDualTriangle
          successor) := by
  classical
  by_cases hexact : successor.CommonNeighborsExact
  · exact Or.inl ⟨appendLocalSuccessor successor left hexact⟩
  · exact Or.inr
      (SeparatedSelectedSourceLocalRailSuccessor.adjacentDualTriangle_of_not_commonNeighborsExact
        successor hexact)

end SelectedSourceLocalRailAssembly

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
