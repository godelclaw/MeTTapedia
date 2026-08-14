import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendCollision

/-!
# L1: loop-erased append for selected local rails

The raw selected-rail append asks each accumulated rail to avoid the tail of
its own continuation in order to keep the concatenation simple.  This is
stronger than the crosscut construction needs: loop erasure turns every
concatenated walk into a path without changing its endpoints.

After applying `Walk.bypass`, only the two crossed old/new support conditions
remain.  They are exactly the conditions needed to keep the first and second
rails mutually disjoint.  The fail-closed alternative below therefore returns
only an actual cross-track collision; a harmless same-track revisit is no
longer promoted to a geometric obstruction.
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
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}

namespace SelectedSourceLocalRailAssembly

variable
    {firstStart secondStart :
      AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}

/-- **L1 loop-erased append.** Extend both selected rails and erase any loop
created by a same-track revisit.  Only cross-track old/new disjointness is
required to preserve mutual rail separation. -/
noncomputable def appendSuccessorBypass
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (assembly : SelectedSourceLocalRailAssembly
      (web := web) firstStart secondStart
      (selectedPlacementSideFace leftPlacement successor.frame.leftBefore)
      (selectedPlacementSideFace leftPlacement successor.frame.leftAfter))
    (hfirstSecond : assembly.firstRail.support.Disjoint
      successor.secondContinuation.support.tail)
    (hsecondFirst : assembly.secondRail.support.Disjoint
      successor.firstContinuation.support.tail) :
    SelectedSourceLocalRailAssembly (web := web) firstStart secondStart
      (selectedPlacementSideFace rightPlacement
        successor.rightOutgoingBefore)
      (selectedPlacementSideFace rightPlacement
        successor.rightOutgoingAfter) where
  firstRail :=
    (assembly.firstRail.append successor.firstContinuation).bypass
  secondRail :=
    (assembly.secondRail.append successor.secondContinuation).bypass
  firstRail_isPath :=
    (assembly.firstRail.append successor.firstContinuation).bypass_isPath
  secondRail_isPath :=
    (assembly.secondRail.append successor.secondContinuation).bypass_isPath
  firstRail_support_disjoint_secondRail := by
    rw [List.disjoint_left]
    intro face hfirst hsecond
    have hfirstRaw :=
      (assembly.firstRail.append successor.firstContinuation
        |>.support_bypass_subset_support) hfirst
    have hsecondRaw :=
      (assembly.secondRail.append successor.secondContinuation
        |>.support_bypass_subset_support) hsecond
    rw [SimpleGraph.Walk.support_append] at hfirstRaw hsecondRaw
    rcases List.mem_append.mp hfirstRaw with hfirstOld | hfirstNew
    · rcases List.mem_append.mp hsecondRaw with hsecondOld | hsecondNew
      · exact (List.disjoint_left.mp
          assembly.firstRail_support_disjoint_secondRail hfirstOld) hsecondOld
      · exact (List.disjoint_left.mp hfirstSecond hfirstOld) hsecondNew
    · rcases List.mem_append.mp hsecondRaw with hsecondOld | hsecondNew
      · exact (List.disjoint_left.mp hsecondFirst hsecondOld) hfirstNew
      · have hfirstFull : face ∈ successor.firstContinuation.support :=
          List.mem_of_mem_tail hfirstNew
        have hsecondFull : face ∈ successor.secondContinuation.support :=
          List.mem_of_mem_tail hsecondNew
        exact (List.disjoint_left.mp
          successor.firstContinuation_support_disjoint_secondContinuation
            hfirstFull) hsecondFull

end SelectedSourceLocalRailAssembly

namespace SeparatedSelectedSourceLocalRailSuccessor

variable
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {leftIncomingBefore leftIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}

/-- A collision between opposite rail tracks at one append. -/
structure ActualCrossAppendCollision
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) where
  face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))
  collision :
    (face ∈ left.paths.firstRail.support ∧
      face ∈ successor.secondContinuation.support.tail) ∨
    (face ∈ left.paths.secondRail.support ∧
      face ∈ successor.firstContinuation.support.tail)

namespace ActualCrossAppendCollision

variable
    {successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement}
    {left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter}

/-- A cross-track collision is, in particular, one of the four actual append
collisions classified by the preceding module. -/
def toActualAppendCollision
    (collision : ActualCrossAppendCollision successor left) :
    ActualAppendCollision successor left :=
  { face := collision.face
    collision := collision.collision.elim
      (fun h => Or.inr (Or.inr (Or.inl h)))
      (fun h => Or.inr (Or.inr (Or.inr h))) }

/-- Every cross-track collision produces the literal adjacent dual triangle. -/
def toAdjacentDualTriangle
    (collision : ActualCrossAppendCollision successor left) :
    AdjacentDualTriangle successor :=
  collision.toActualAppendCollision.toAdjacentDualTriangle

end ActualCrossAppendCollision

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

/-- **L1 exact loop-erased adjacent alternative.** Same-track revisits are
erased.  The bad branch contains only an actual collision between opposite
rail tracks. -/
noncomputable def appendLocalSuccessorBypass_or_crossCollision
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
    Nonempty (SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision
      successor left) := by
  classical
  by_cases hfirstSecond : left.paths.firstRail.support.Disjoint
      successor.secondContinuation.support.tail
  · by_cases hsecondFirst : left.paths.secondRail.support.Disjoint
        successor.firstContinuation.support.tail
    · exact Or.inl ⟨appendSuccessorBypass successor left.toAssembly
        hfirstSecond hsecondFirst⟩
    · rw [List.disjoint_left] at hsecondFirst
      push Not at hsecondFirst
      rcases hsecondFirst with ⟨face, hleft, hright⟩
      exact Or.inr ⟨⟨face, Or.inr ⟨hleft, hright⟩⟩⟩
  · rw [List.disjoint_left] at hfirstSecond
    push Not at hfirstSecond
    rcases hfirstSecond with ⟨face, hleft, hright⟩
    exact Or.inr ⟨⟨face, Or.inl ⟨hleft, hright⟩⟩⟩

/-- Consumer form of the loop-erased fork. -/
noncomputable def appendLocalSuccessorBypass_or_actualAdjacentDualTriangle
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
  rcases appendLocalSuccessorBypass_or_crossCollision successor left with
    assembly | collision
  · exact Or.inl assembly
  · rcases collision with ⟨collision⟩
    exact Or.inr ⟨collision.toAdjacentDualTriangle⟩

end SelectedSourceLocalRailAssembly

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
