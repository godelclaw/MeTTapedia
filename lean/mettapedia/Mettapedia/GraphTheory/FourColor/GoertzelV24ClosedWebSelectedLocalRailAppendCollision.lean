import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendObstruction

/-!
# L1: actual support collision at one selected rail append

`CommonNeighborsExact` is a sufficient local condition for appending two
selected Cell--3 rail pairs, but its failure may exhibit a third common face
which neither rail actually uses.  This module tests the four support
conditions consumed by `appendSuccessor` directly.

The resulting alternative is exact: either the two-cell assembly is
constructed, or a face occurring in an actual old/new support collision is
returned.  Every such face is proved to be the third vertex of the same
facial-dual obstruction triangle.  Thus irrelevant common neighbours no
longer block the construction, while a genuine collision remains positive
geometric data rather than a negated hypothesis.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
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
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}

private theorem start_not_mem_support_tail_of_isPath
    {F : Type*} {H : SimpleGraph F} {start finish : F}
    (walk : H.Walk start finish) (hpath : walk.IsPath) :
    start ∉ walk.support.tail := by
  have hnodup := hpath.support_nodup
  rw [← walk.cons_tail_support] at hnodup
  exact (List.nodup_cons.mp hnodup).1

private theorem end_mem_support
    {F : Type*} {H : SimpleGraph F} {start finish : F}
    (walk : H.Walk start finish) : finish ∈ walk.support := by
  simp

namespace SeparatedSelectedSourceLocalRailSuccessor

variable
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {leftIncomingBefore leftIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}

/-- A face witnessing one of the four actual support collisions that would
invalidate the next append. -/
structure ActualAppendCollision
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) where
  face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))
  collision :
    (face ∈ left.paths.firstRail.support ∧
      face ∈ successor.firstContinuation.support.tail) ∨
    (face ∈ left.paths.secondRail.support ∧
      face ∈ successor.secondContinuation.support.tail) ∨
    (face ∈ left.paths.firstRail.support ∧
      face ∈ successor.secondContinuation.support.tail) ∨
    (face ∈ left.paths.secondRail.support ∧
      face ∈ successor.firstContinuation.support.tail)

namespace ActualAppendCollision

variable
    {successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement}
    {left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter}

/-- Every actual append collision is a third common neighbour of the two
consecutive corridor centres and is distinct from both literal seam flanks. -/
def toAdjacentDualTriangle
    (collision : ActualAppendCollision successor left) :
    AdjacentDualTriangle successor := by
  have hleftAdj :
      (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        ((corridor.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center)
        collision.face := by
    rcases collision.collision with h | h | h | h
    · exact left.paths.firstRail_support_adjacent_center collision.face h.1
    · exact left.paths.secondRail_support_adjacent_center collision.face h.1
    · exact left.paths.firstRail_support_adjacent_center collision.face h.1
    · exact left.paths.secondRail_support_adjacent_center collision.face h.1
  have hrightAdj :
      (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        ((corridor.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton).faceAt
            (nextCorridorInterior leftInterior hnext).center)
        collision.face := by
    rcases collision.collision with h | h | h | h
    · apply successor.rightRails.paths.firstRail_support_adjacent_center
      rw [← successor.firstContinuation_support]
      exact List.mem_of_mem_tail h.2
    · apply successor.rightRails.paths.secondRail_support_adjacent_center
      rw [← successor.secondContinuation_support]
      exact List.mem_of_mem_tail h.2
    · apply successor.rightRails.paths.secondRail_support_adjacent_center
      rw [← successor.secondContinuation_support]
      exact List.mem_of_mem_tail h.2
    · apply successor.rightRails.paths.firstRail_support_adjacent_center
      rw [← successor.firstContinuation_support]
      exact List.mem_of_mem_tail h.2
  have hneBefore : collision.face ≠
      selectedPlacementSideFace leftPlacement successor.frame.leftBefore := by
    intro heq
    rcases collision.collision with h | h | h | h
    · apply start_not_mem_support_tail_of_isPath successor.firstContinuation
        successor.firstContinuation_isPath
      simpa [heq] using h.2
    · have hfirstEnd : selectedPlacementSideFace leftPlacement
          successor.frame.leftBefore ∈ left.paths.firstRail.support :=
        end_mem_support left.paths.firstRail
      exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
        hfirstEnd) (by simpa [heq] using h.1)
    · have hfirstStart : selectedPlacementSideFace leftPlacement
          successor.frame.leftBefore ∈
          successor.rightRails.paths.firstRail.support := by
        rw [successor.frame.leftBeforeFace_eq_rightAfterFace]
        exact successor.rightRails.paths.firstRail.start_mem_support
      have hsecondFull : collision.face ∈
          successor.rightRails.paths.secondRail.support := by
        rw [← successor.secondContinuation_support]
        exact List.mem_of_mem_tail h.2
      exact (List.disjoint_left.mp
        successor.rightRails.firstRail_support_disjoint_secondRail
        hfirstStart) (by simpa [heq] using hsecondFull)
    · have hfirstEnd : selectedPlacementSideFace leftPlacement
          successor.frame.leftBefore ∈ left.paths.firstRail.support :=
        end_mem_support left.paths.firstRail
      exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
        hfirstEnd) (by simpa [heq] using h.1)
  have hneAfter : collision.face ≠
      selectedPlacementSideFace leftPlacement successor.frame.leftAfter := by
    intro heq
    rcases collision.collision with h | h | h | h
    · have hsecondEnd : selectedPlacementSideFace leftPlacement
          successor.frame.leftAfter ∈ left.paths.secondRail.support :=
        end_mem_support left.paths.secondRail
      exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
        (by simpa [heq] using h.1)) hsecondEnd
    · apply start_not_mem_support_tail_of_isPath successor.secondContinuation
        successor.secondContinuation_isPath
      simpa [heq] using h.2
    · have hsecondEnd : selectedPlacementSideFace leftPlacement
          successor.frame.leftAfter ∈ left.paths.secondRail.support :=
        end_mem_support left.paths.secondRail
      exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
        (by simpa [heq] using h.1)) hsecondEnd
    · have hsecondStart : selectedPlacementSideFace leftPlacement
          successor.frame.leftAfter ∈
          successor.rightRails.paths.secondRail.support := by
        rw [successor.frame.leftAfterFace_eq_rightBeforeFace]
        exact successor.rightRails.paths.secondRail.start_mem_support
      have hfirstFull : collision.face ∈
          successor.rightRails.paths.firstRail.support := by
        rw [← successor.firstContinuation_support]
        exact List.mem_of_mem_tail h.2
      exact (List.disjoint_left.mp
        successor.rightRails.firstRail_support_disjoint_secondRail
        (by simpa [heq] using hfirstFull)) hsecondStart
  exact {
    third := collision.face
    leftCenter_adj_third := hleftAdj
    rightCenter_adj_third := hrightAdj
    third_ne_before := hneBefore
    third_ne_after := hneAfter
  }

end ActualAppendCollision

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

/-- **L1 exact adjacent append alternative.** Test exactly the four support
conditions consumed by `appendSuccessor`.  The bad branch carries a face from
an actual collision, not merely an unused common neighbour. -/
noncomputable def appendLocalSuccessor_or_actualCollision
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) :
    Nonempty (SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)) ∨
    Nonempty (SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
      successor left) := by
  classical
  by_cases hfirstPath : left.paths.firstRail.support.Disjoint
      successor.firstContinuation.support.tail
  · by_cases hsecondPath : left.paths.secondRail.support.Disjoint
        successor.secondContinuation.support.tail
    · by_cases hfirstSecond : left.paths.firstRail.support.Disjoint
          successor.secondContinuation.support.tail
      · by_cases hsecondFirst : left.paths.secondRail.support.Disjoint
            successor.firstContinuation.support.tail
        · exact Or.inl ⟨appendSuccessor successor left.toAssembly
            hfirstPath hsecondPath hfirstSecond hsecondFirst⟩
        · rw [List.disjoint_left] at hsecondFirst
          push Not at hsecondFirst
          rcases hsecondFirst with ⟨face, hleft, hright⟩
          exact Or.inr ⟨⟨face, Or.inr (Or.inr (Or.inr ⟨hleft, hright⟩))⟩⟩
      · rw [List.disjoint_left] at hfirstSecond
        push Not at hfirstSecond
        rcases hfirstSecond with ⟨face, hleft, hright⟩
        exact Or.inr ⟨⟨face, Or.inr (Or.inr (Or.inl ⟨hleft, hright⟩))⟩⟩
    · rw [List.disjoint_left] at hsecondPath
      push Not at hsecondPath
      rcases hsecondPath with ⟨face, hleft, hright⟩
      exact Or.inr ⟨⟨face, Or.inr (Or.inl ⟨hleft, hright⟩)⟩⟩
  · rw [List.disjoint_left] at hfirstPath
    push Not at hfirstPath
    rcases hfirstPath with ⟨face, hleft, hright⟩
    exact Or.inr ⟨⟨face, Or.inl ⟨hleft, hright⟩⟩⟩

/-- Consumer form: the exact append either succeeds, or its actual collision
produces the literal facial-dual triangle used by the separator analysis. -/
noncomputable def appendLocalSuccessor_or_actualAdjacentDualTriangle
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) :
    Nonempty (SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)) ∨
    Nonempty (SeparatedSelectedSourceLocalRailSuccessor.AdjacentDualTriangle
      successor) := by
  rcases appendLocalSuccessor_or_actualCollision successor left with
    assembly | collision
  · exact Or.inl assembly
  · exact Or.inr ⟨collision.some.toAdjacentDualTriangle⟩

end SelectedSourceLocalRailAssembly

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
