import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendSwap

/-!
# L1: exhaustive classification of one selected local rail append

The loop-erased straight append consumes the two cross-track separation
tests.  If both cross-track tests instead exhibit collisions, the endpoint
swap consumes the two same-track separation tests.  This file performs the
complete binary classification and retains an actual face whenever a support
test fails.

There are four outcomes: a straight assembly, a swapped assembly, exactly one
cross-track collision, or two cross-track collisions together with a
same-track collision.  Thus no failed Boolean support test is hidden in an
assumption.  The last two outcomes remain genuine local residues: this file
does not prove arbitrary corridor assembly, attach either annular end cap, or
close Fable flag L1.
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

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
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

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- An exhibited common face of two rail-support lists. -/
structure SelectedRailSupportCollision
    (oldSupport newSupport : List (SelectedFace (web := web))) where
  face : SelectedFace (web := web)
  mem_old : face ∈ oldSupport
  mem_new : face ∈ newSupport

namespace SelectedRailSupportCollision

/-- Failure of list disjointness returns the face that witnesses it. -/
noncomputable def of_not_disjoint
    {oldSupport newSupport : List (SelectedFace (web := web))}
    (hcollision : ¬ oldSupport.Disjoint newSupport) :
    SelectedRailSupportCollision (web := web) oldSupport newSupport := by
  classical
  rw [List.disjoint_left] at hcollision
  push Not at hcollision
  let face := Classical.choose hcollision
  have hface := Classical.choose_spec hcollision
  exact ⟨face, hface.1, hface.2⟩

end SelectedRailSupportCollision

namespace SelectedSourceLocalRailAssembly

variable
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {leftIncomingBefore leftIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}

/-- **L1 finite adjacent classification.** The exhaustive result of trying
to append one selected literal Cell-3 rail pair.

The two constructive cases retain the complete resulting assembly.  The two
residual cases retain every failed support test as a face witness, so a later
local classification can consume the geometry without recovering it from a
negated proposition. -/
inductive SelectedLocalRailAppendOutcome
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) : Type (u + 1)
  | straight
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace leftPlacement leftIncomingBefore)
        (selectedPlacementSideFace leftPlacement leftIncomingAfter)
        (selectedPlacementSideFace rightPlacement
          successor.rightOutgoingBefore)
        (selectedPlacementSideFace rightPlacement
          successor.rightOutgoingAfter))
  | swapped
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace leftPlacement leftIncomingBefore)
        (selectedPlacementSideFace leftPlacement leftIncomingAfter)
        (selectedPlacementSideFace rightPlacement
          successor.rightOutgoingAfter)
        (selectedPlacementSideFace rightPlacement
          successor.rightOutgoingBefore))
  | singleFirstSecond
      (collision : SelectedRailSupportCollision (web := web)
        left.paths.firstRail.support
        successor.secondContinuation.support.tail)
      (otherCrossDisjoint : left.paths.secondRail.support.Disjoint
        successor.firstContinuation.support.tail)
  | singleSecondFirst
      (collision : SelectedRailSupportCollision (web := web)
        left.paths.secondRail.support
        successor.firstContinuation.support.tail)
      (otherCrossDisjoint : left.paths.firstRail.support.Disjoint
        successor.secondContinuation.support.tail)
  | doubleCrossSameTrack
      (firstSecondCollision : SelectedRailSupportCollision (web := web)
        left.paths.firstRail.support
        successor.secondContinuation.support.tail)
      (secondFirstCollision : SelectedRailSupportCollision (web := web)
        left.paths.secondRail.support
        successor.firstContinuation.support.tail)
      (sameTrackCollision :
        SelectedRailSupportCollision (web := web)
            left.paths.firstRail.support
            successor.firstContinuation.support.tail ⊕
          SelectedRailSupportCollision (web := web)
            left.paths.secondRail.support
            successor.secondContinuation.support.tail)

/-- **L1 exhaustive adjacent append classifier.** Every selected neighbouring
pair constructs a straight assembly, constructs a swapped assembly, or returns
one of the two exact collision residues displayed by
`SelectedLocalRailAppendOutcome`.

This theorem is a finite local classification interface, not a proof that the
two residual cases are impossible. -/
noncomputable def classifyLocalSuccessorAppend
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) :
    SelectedLocalRailAppendOutcome successor left := by
  classical
  by_cases hfirstSecond : left.paths.firstRail.support.Disjoint
      successor.secondContinuation.support.tail
  · by_cases hsecondFirst : left.paths.secondRail.support.Disjoint
        successor.firstContinuation.support.tail
    · exact .straight
        (appendSuccessorBypass successor left.toAssembly
          hfirstSecond hsecondFirst)
    · exact .singleSecondFirst
        (SelectedRailSupportCollision.of_not_disjoint hsecondFirst)
        hfirstSecond
  · let firstSecondCollision : SelectedRailSupportCollision (web := web)
        left.paths.firstRail.support
        successor.secondContinuation.support.tail :=
      SelectedRailSupportCollision.of_not_disjoint hfirstSecond
    by_cases hsecondFirst : left.paths.secondRail.support.Disjoint
        successor.firstContinuation.support.tail
    · exact .singleFirstSecond firstSecondCollision hsecondFirst
    · let secondFirstCollision : SelectedRailSupportCollision (web := web)
          left.paths.secondRail.support
          successor.firstContinuation.support.tail :=
        SelectedRailSupportCollision.of_not_disjoint hsecondFirst
      by_cases hfirstFirst : left.paths.firstRail.support.Disjoint
          successor.firstContinuation.support.tail
      · by_cases hsecondSecond : left.paths.secondRail.support.Disjoint
            successor.secondContinuation.support.tail
        · exact .swapped
            (appendSuccessorSwapBothCrossCollisions successor left
              firstSecondCollision.face secondFirstCollision.face
              firstSecondCollision.mem_old firstSecondCollision.mem_new
              secondFirstCollision.mem_old secondFirstCollision.mem_new
              hfirstFirst hsecondSecond)
        · exact .doubleCrossSameTrack firstSecondCollision
            secondFirstCollision
            (Sum.inr
              (SelectedRailSupportCollision.of_not_disjoint hsecondSecond))
      · exact .doubleCrossSameTrack firstSecondCollision
          secondFirstCollision
          (Sum.inl (SelectedRailSupportCollision.of_not_disjoint hfirstFirst))

end SelectedSourceLocalRailAssembly

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
