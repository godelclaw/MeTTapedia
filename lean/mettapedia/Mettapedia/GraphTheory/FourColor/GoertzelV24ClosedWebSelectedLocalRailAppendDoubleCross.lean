import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendClassification

/-!
# L1: exclude the mixed double-cross append residue

If both cross-track support tests collide, all four local rails are
nonstationary.  Each selected Cell-3 pair has total rail length at most two,
so all four rails then have length exactly one.  A further same-track
collision would identify the same incoming face with both outgoing faces,
contradicting the right pair's support disjointness.

Consequently the exhaustive adjacent classifier has only three live
outcomes: straight, swapped, or exactly one cross-track collision.  This is a
local length-and-endpoint argument.  It does not discharge the lone-cross
case, iterate a corridor, attach either annular end cap, or close Fable flag
L1.
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
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}

private theorem walk_length_pos_of_mem_support_of_ne_end
    {F : Type*} {H : SimpleGraph F} {start finish face : F}
    (walk : H.Walk start finish) (hface : face ∈ walk.support)
    (hne : face ≠ finish) : 0 < walk.length := by
  cases walk with
  | nil =>
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hface
      exact False.elim (hne hface)
  | cons => simp

private theorem walk_length_pos_of_mem_support_tail
    {F : Type*} {H : SimpleGraph F} {start finish face : F}
    (walk : H.Walk start finish) (hface : face ∈ walk.support.tail) :
    0 < walk.length := by
  cases walk with
  | nil => simp at hface
  | cons => simp

private theorem walk_mem_support_eq_start_or_end_of_length_le_one
    {F : Type*} {H : SimpleGraph F} {start finish face : F}
    (walk : H.Walk start finish) (hlength : walk.length ≤ 1)
    (hface : face ∈ walk.support) : face = start ∨ face = finish := by
  cases walk with
  | nil => simpa using hface
  | cons hadj tail =>
      cases tail with
      | nil => simpa using hface
      | cons hnext rest =>
          simp only [SimpleGraph.Walk.length_cons] at hlength
          omega

private theorem start_not_mem_support_tail_of_isPath
    {F : Type*} {H : SimpleGraph F} {start finish : F}
    (walk : H.Walk start finish) (hpath : walk.IsPath) :
    start ∉ walk.support.tail := by
  have hnodup := hpath.support_nodup
  rw [← walk.cons_tail_support] at hnodup
  exact (List.nodup_cons.mp hnodup).1

private theorem eq_end_of_mem_support_tail_of_length_le_one
    {F : Type*} {H : SimpleGraph F} {start finish face : F}
    (walk : H.Walk start finish) (hpath : walk.IsPath)
    (hlength : walk.length ≤ 1) (hface : face ∈ walk.support.tail) :
    face = finish := by
  rcases walk_mem_support_eq_start_or_end_of_length_le_one walk hlength
      (List.mem_of_mem_tail hface) with hstart | hend
  · exact False.elim
      (start_not_mem_support_tail_of_isPath walk hpath (hstart ▸ hface))
  · exact hend

namespace SelectedSourceLocalRailAssembly

variable
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {leftIncomingBefore leftIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}
    {successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement}
    {left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter}

/-- Two cross-track collisions cannot coexist with a same-track collision in
one selected adjacent Cell-3 append. -/
theorem not_doubleCrossSameTrack
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
          successor.secondContinuation.support.tail) : False := by
  let firstSecondActual :
      SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
        successor left := {
    face := firstSecondCollision.face
    collision := Or.inr (Or.inr (Or.inl
      ⟨firstSecondCollision.mem_old, firstSecondCollision.mem_new⟩))
  }
  let secondFirstActual :
      SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
        successor left := {
    face := secondFirstCollision.face
    collision := Or.inr (Or.inr (Or.inr
      ⟨secondFirstCollision.mem_old, secondFirstCollision.mem_new⟩))
  }
  have hleftFirstPos : 0 < left.paths.firstRail.length :=
    walk_length_pos_of_mem_support_of_ne_end left.paths.firstRail
      firstSecondCollision.mem_old
      firstSecondActual.toAdjacentDualTriangle.third_ne_before
  have hleftSecondPos : 0 < left.paths.secondRail.length :=
    walk_length_pos_of_mem_support_of_ne_end left.paths.secondRail
      secondFirstCollision.mem_old
      secondFirstActual.toAdjacentDualTriangle.third_ne_after
  have hrightFirstContinuationPos : 0 < successor.firstContinuation.length :=
    walk_length_pos_of_mem_support_tail successor.firstContinuation
      secondFirstCollision.mem_new
  have hrightSecondContinuationPos : 0 < successor.secondContinuation.length :=
    walk_length_pos_of_mem_support_tail successor.secondContinuation
      firstSecondCollision.mem_new
  have hrightFirstPos : 0 < successor.rightRails.paths.firstRail.length := by
    simpa [SeparatedSelectedSourceLocalRailSuccessor.firstContinuation] using
      hrightFirstContinuationPos
  have hrightSecondPos : 0 < successor.rightRails.paths.secondRail.length := by
    simpa [SeparatedSelectedSourceLocalRailSuccessor.secondContinuation] using
      hrightSecondContinuationPos
  have hleftSum := left.paths.firstRail_length_add_secondRail_length_le_two
  have hrightSum :=
    successor.rightRails.paths.firstRail_length_add_secondRail_length_le_two
  have hleftFirstLe : left.paths.firstRail.length ≤ 1 := by
    omega
  have hleftSecondLe : left.paths.secondRail.length ≤ 1 := by
    omega
  have hrightFirstLe : successor.firstContinuation.length ≤ 1 := by
    simpa [SeparatedSelectedSourceLocalRailSuccessor.firstContinuation] using
      (show successor.rightRails.paths.firstRail.length ≤ 1 by omega)
  have hrightSecondLe : successor.secondContinuation.length ≤ 1 := by
    simpa [SeparatedSelectedSourceLocalRailSuccessor.secondContinuation] using
      (show successor.rightRails.paths.secondRail.length ≤ 1 by omega)
  have hfirstSecondOldStart : firstSecondCollision.face =
      selectedPlacementSideFace leftPlacement leftIncomingBefore := by
    rcases walk_mem_support_eq_start_or_end_of_length_le_one
        left.paths.firstRail hleftFirstLe firstSecondCollision.mem_old with
      hstart | hend
    · exact hstart
    · exact False.elim
        (firstSecondActual.toAdjacentDualTriangle.third_ne_before hend)
  have hfirstSecondNewEnd : firstSecondCollision.face =
      selectedPlacementSideFace rightPlacement
        successor.rightOutgoingAfter :=
    eq_end_of_mem_support_tail_of_length_le_one successor.secondContinuation
      successor.secondContinuation_isPath hrightSecondLe
      firstSecondCollision.mem_new
  have hsecondFirstOldStart : secondFirstCollision.face =
      selectedPlacementSideFace leftPlacement leftIncomingAfter := by
    rcases walk_mem_support_eq_start_or_end_of_length_le_one
        left.paths.secondRail hleftSecondLe secondFirstCollision.mem_old with
      hstart | hend
    · exact hstart
    · exact False.elim
        (secondFirstActual.toAdjacentDualTriangle.third_ne_after hend)
  have hsecondFirstNewEnd : secondFirstCollision.face =
      selectedPlacementSideFace rightPlacement
        successor.rightOutgoingBefore :=
    eq_end_of_mem_support_tail_of_length_le_one successor.firstContinuation
      successor.firstContinuation_isPath hrightFirstLe
      secondFirstCollision.mem_new
  rcases sameTrackCollision with firstFirstCollision | secondSecondCollision
  · let firstFirstActual :
        SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
          successor left := {
      face := firstFirstCollision.face
      collision := Or.inl
        ⟨firstFirstCollision.mem_old, firstFirstCollision.mem_new⟩
    }
    have hsameOldStart : firstFirstCollision.face =
        selectedPlacementSideFace leftPlacement leftIncomingBefore := by
      rcases walk_mem_support_eq_start_or_end_of_length_le_one
          left.paths.firstRail hleftFirstLe firstFirstCollision.mem_old with
        hstart | hend
      · exact hstart
      · exact False.elim
          (firstFirstActual.toAdjacentDualTriangle.third_ne_before hend)
    have hsameNewEnd : firstFirstCollision.face =
        selectedPlacementSideFace rightPlacement
          successor.rightOutgoingBefore :=
      eq_end_of_mem_support_tail_of_length_le_one successor.firstContinuation
        successor.firstContinuation_isPath hrightFirstLe
        firstFirstCollision.mem_new
    have houtgoingEq :
        selectedPlacementSideFace rightPlacement
            successor.rightOutgoingBefore =
          selectedPlacementSideFace rightPlacement
            successor.rightOutgoingAfter := by
      calc
        selectedPlacementSideFace rightPlacement
            successor.rightOutgoingBefore = firstFirstCollision.face :=
          hsameNewEnd.symm
        _ = selectedPlacementSideFace leftPlacement leftIncomingBefore :=
          hsameOldStart
        _ = firstSecondCollision.face := hfirstSecondOldStart.symm
        _ = selectedPlacementSideFace rightPlacement
            successor.rightOutgoingAfter := hfirstSecondNewEnd
    have hfirstEnd := successor.rightRails.paths.firstRail.end_mem_support
    have hsecondEnd := successor.rightRails.paths.secondRail.end_mem_support
    exact (List.disjoint_left.mp
      successor.rightRails.firstRail_support_disjoint_secondRail hfirstEnd)
        (by rw [houtgoingEq]; exact hsecondEnd)
  · let secondSecondActual :
        SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
          successor left := {
      face := secondSecondCollision.face
      collision := Or.inr (Or.inl
        ⟨secondSecondCollision.mem_old, secondSecondCollision.mem_new⟩)
    }
    have hsameOldStart : secondSecondCollision.face =
        selectedPlacementSideFace leftPlacement leftIncomingAfter := by
      rcases walk_mem_support_eq_start_or_end_of_length_le_one
          left.paths.secondRail hleftSecondLe secondSecondCollision.mem_old with
        hstart | hend
      · exact hstart
      · exact False.elim
          (secondSecondActual.toAdjacentDualTriangle.third_ne_after hend)
    have hsameNewEnd : secondSecondCollision.face =
        selectedPlacementSideFace rightPlacement
          successor.rightOutgoingAfter :=
      eq_end_of_mem_support_tail_of_length_le_one successor.secondContinuation
        successor.secondContinuation_isPath hrightSecondLe
        secondSecondCollision.mem_new
    have houtgoingEq :
        selectedPlacementSideFace rightPlacement
            successor.rightOutgoingBefore =
          selectedPlacementSideFace rightPlacement
            successor.rightOutgoingAfter := by
      calc
        selectedPlacementSideFace rightPlacement
            successor.rightOutgoingBefore = secondFirstCollision.face :=
          hsecondFirstNewEnd.symm
        _ = selectedPlacementSideFace leftPlacement leftIncomingAfter :=
          hsecondFirstOldStart
        _ = secondSecondCollision.face := hsameOldStart.symm
        _ = selectedPlacementSideFace rightPlacement
            successor.rightOutgoingAfter := hsameNewEnd
    have hfirstEnd := successor.rightRails.paths.firstRail.end_mem_support
    have hsecondEnd := successor.rightRails.paths.secondRail.end_mem_support
    exact (List.disjoint_left.mp
      successor.rightRails.firstRail_support_disjoint_secondRail hfirstEnd)
        (by rw [houtgoingEq]; exact hsecondEnd)

/-- The refined exhaustive result after excluding the mixed double-cross
case.  The lone-cross constructors are now the only unresolved local
outcomes. -/
inductive SelectedLocalRailAppendResolvedOutcome
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

/-- **L1 refined exhaustive adjacent classifier.** The double-cross case is
always constructively swapped; the only remaining local residue is exactly
one cross-track collision. -/
noncomputable def classifyLocalSuccessorAppendResolved
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) :
    SelectedLocalRailAppendResolvedOutcome successor left :=
  match classifyLocalSuccessorAppend successor left with
  | .straight assembly => .straight assembly
  | .swapped assembly => .swapped assembly
  | .singleFirstSecond collision hother =>
      .singleFirstSecond collision hother
  | .singleSecondFirst collision hother =>
      .singleSecondFirst collision hother
  | .doubleCrossSameTrack firstSecond secondFirst sameTrack =>
      False.elim (not_doubleCrossSameTrack firstSecond secondFirst sameTrack)

end SelectedSourceLocalRailAssembly

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
