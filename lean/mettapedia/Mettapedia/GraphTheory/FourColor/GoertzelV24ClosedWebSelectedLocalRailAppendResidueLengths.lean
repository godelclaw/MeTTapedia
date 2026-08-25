import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendCenterBridge

/-!
# L1: exact length shapes of the centre-bridge residues

The centre-bridge classifier leaves only same-track revisits or a continuation
which contains the previous Cell-3 centre.  This file retains the original
cross-collision provenance and applies the per-cell total-length bound.  Every
residue is forced into one of the extreme `2+0`, `1+1`, or `0+2` shapes.

These equations are the finite input for the next coordinate/rerouting audit.
They do not themselves construct the final adjacent assembly, iterate a
corridor, attach annular end caps, or close Fable flag L1.
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

private theorem length_eq_two_of_two_distinct_mem_ne_end
    {F : Type*} {H : SimpleGraph F} {start finish first second : F}
    (walk : H.Walk start finish) (hlength : walk.length ≤ 2)
    (hfirst : first ∈ walk.support) (hsecond : second ∈ walk.support)
    (hne : first ≠ second) (hfirstEnd : first ≠ finish)
    (hsecondEnd : second ≠ finish) : walk.length = 2 := by
  by_contra hnot
  have hle : walk.length ≤ 1 := by omega
  rcases walk_mem_support_eq_start_or_end_of_length_le_one walk hle hfirst with
    hfirstStart | hfirstFinish
  · rcases walk_mem_support_eq_start_or_end_of_length_le_one walk hle hsecond with
      hsecondStart | hsecondFinish
    · exact hne (hfirstStart.trans hsecondStart.symm)
    · exact hsecondEnd hsecondFinish
  · exact hfirstEnd hfirstFinish

private theorem length_eq_two_of_two_distinct_mem_tail
    {F : Type*} {H : SimpleGraph F} {start finish first second : F}
    (walk : H.Walk start finish) (hpath : walk.IsPath)
    (hlength : walk.length ≤ 2)
    (hfirst : first ∈ walk.support.tail)
    (hsecond : second ∈ walk.support.tail) (hne : first ≠ second) :
    walk.length = 2 := by
  by_contra hnot
  have hle : walk.length ≤ 1 := by omega
  have hfirstEnd := eq_end_of_mem_support_tail_of_length_le_one
    walk hpath hle hfirst
  have hsecondEnd := eq_end_of_mem_support_tail_of_length_le_one
    walk hpath hle hsecond
  exact hne (hfirstEnd.trans hsecondEnd.symm)

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

private theorem firstContinuation_length_le_two :
    successor.firstContinuation.length ≤ 2 := by
  simpa [SeparatedSelectedSourceLocalRailSuccessor.firstContinuation] using
    successor.rightRails.paths.firstRail_length_le_two

private theorem secondContinuation_length_le_two :
    successor.secondContinuation.length ≤ 2 := by
  simpa [SeparatedSelectedSourceLocalRailSuccessor.secondContinuation] using
    successor.rightRails.paths.secondRail_length_le_two

private theorem continuation_length_sum_le_two :
    successor.firstContinuation.length + successor.secondContinuation.length ≤ 2 := by
  simpa [SeparatedSelectedSourceLocalRailSuccessor.firstContinuation,
    SeparatedSelectedSourceLocalRailSuccessor.secondContinuation] using
      successor.rightRails.paths.firstRail_length_add_secondRail_length_le_two

private def firstSecondActual
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.secondContinuation.support.tail) :
    SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision
      successor left :=
  ⟨collision.face, Or.inl ⟨collision.mem_old, collision.mem_new⟩⟩

private def secondFirstActual
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.firstContinuation.support.tail) :
    SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision
      successor left :=
  ⟨collision.face, Or.inr ⟨collision.mem_old, collision.mem_new⟩⟩

private theorem firstSecond_sameFirst_lengths
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.secondContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.firstContinuation.support.tail) :
    left.paths.firstRail.length = 2 ∧
      left.paths.secondRail.length = 0 ∧
      successor.firstContinuation.length = 1 ∧
      successor.secondContinuation.length = 1 := by
  let sameActual : SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
      successor left := ⟨same.face, Or.inl ⟨same.mem_old, same.mem_new⟩⟩
  have hfacesNe : cross.face ≠ same.face := by
    intro heq
    exact (List.disjoint_left.mp
      successor.firstContinuation_support_disjoint_secondContinuation
        (List.mem_of_mem_tail (heq ▸ same.mem_new)))
      (List.mem_of_mem_tail cross.mem_new)
  have hleftTwo := length_eq_two_of_two_distinct_mem_ne_end
    left.paths.firstRail left.paths.firstRail_length_le_two
    cross.mem_old same.mem_old hfacesNe
    (firstSecondActual cross).toAdjacentDualTriangle.third_ne_before
    sameActual.toAdjacentDualTriangle.third_ne_before
  have hrightFirstPos := walk_length_pos_of_mem_support_tail
    successor.firstContinuation same.mem_new
  have hrightSecondPos := walk_length_pos_of_mem_support_tail
    successor.secondContinuation cross.mem_new
  have hleftSum := left.paths.firstRail_length_add_secondRail_length_le_two
  have hrightSum := continuation_length_sum_le_two (successor := successor)
  exact ⟨hleftTwo, by omega, by omega, by omega⟩

private theorem firstSecond_sameSecond_lengths
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.secondContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.secondContinuation.support.tail) :
    left.paths.firstRail.length = 1 ∧
      left.paths.secondRail.length = 1 ∧
      successor.firstContinuation.length = 0 ∧
      successor.secondContinuation.length = 2 := by
  have hfacesNe : cross.face ≠ same.face := by
    intro heq
    exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
      cross.mem_old) (heq ▸ same.mem_old)
  have hrightTwo := length_eq_two_of_two_distinct_mem_tail
    successor.secondContinuation successor.secondContinuation_isPath
    (secondContinuation_length_le_two (successor := successor))
    cross.mem_new same.mem_new hfacesNe
  have hleftFirstPos := walk_length_pos_of_mem_support_of_ne_end
    left.paths.firstRail cross.mem_old
    (firstSecondActual cross).toAdjacentDualTriangle.third_ne_before
  let sameActual : SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
      successor left := ⟨same.face, Or.inr (Or.inl
        ⟨same.mem_old, same.mem_new⟩)⟩
  have hleftSecondPos := walk_length_pos_of_mem_support_of_ne_end
    left.paths.secondRail same.mem_old
    sameActual.toAdjacentDualTriangle.third_ne_after
  have hleftSum := left.paths.firstRail_length_add_secondRail_length_le_two
  have hrightSum := continuation_length_sum_le_two (successor := successor)
  exact ⟨by omega, by omega, by omega, hrightTwo⟩

private theorem secondFirst_sameFirst_lengths
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.firstContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.firstContinuation.support.tail) :
    left.paths.firstRail.length = 1 ∧
      left.paths.secondRail.length = 1 ∧
      successor.firstContinuation.length = 2 ∧
      successor.secondContinuation.length = 0 := by
  have hfacesNe : cross.face ≠ same.face := by
    intro heq
    exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
      (heq ▸ same.mem_old)) cross.mem_old
  have hrightTwo := length_eq_two_of_two_distinct_mem_tail
    successor.firstContinuation successor.firstContinuation_isPath
    (firstContinuation_length_le_two (successor := successor))
    cross.mem_new same.mem_new hfacesNe
  have hleftSecondPos := walk_length_pos_of_mem_support_of_ne_end
    left.paths.secondRail cross.mem_old
    (secondFirstActual cross).toAdjacentDualTriangle.third_ne_after
  let sameActual : SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
      successor left := ⟨same.face, Or.inl ⟨same.mem_old, same.mem_new⟩⟩
  have hleftFirstPos := walk_length_pos_of_mem_support_of_ne_end
    left.paths.firstRail same.mem_old
    sameActual.toAdjacentDualTriangle.third_ne_before
  have hleftSum := left.paths.firstRail_length_add_secondRail_length_le_two
  have hrightSum := continuation_length_sum_le_two (successor := successor)
  exact ⟨by omega, by omega, hrightTwo, by omega⟩

private theorem secondFirst_sameSecond_lengths
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.firstContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.secondContinuation.support.tail) :
    left.paths.firstRail.length = 0 ∧
      left.paths.secondRail.length = 2 ∧
      successor.firstContinuation.length = 1 ∧
      successor.secondContinuation.length = 1 := by
  let sameActual : SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
      successor left := ⟨same.face, Or.inr (Or.inl
        ⟨same.mem_old, same.mem_new⟩)⟩
  have hfacesNe : cross.face ≠ same.face := by
    intro heq
    exact (List.disjoint_left.mp
      successor.firstContinuation_support_disjoint_secondContinuation
        (List.mem_of_mem_tail cross.mem_new))
      (List.mem_of_mem_tail (heq ▸ same.mem_new))
  have hleftTwo := length_eq_two_of_two_distinct_mem_ne_end
    left.paths.secondRail left.paths.secondRail_length_le_two
    cross.mem_old same.mem_old hfacesNe
    (secondFirstActual cross).toAdjacentDualTriangle.third_ne_after
    sameActual.toAdjacentDualTriangle.third_ne_after
  have hrightFirstPos := walk_length_pos_of_mem_support_tail
    successor.firstContinuation cross.mem_new
  have hrightSecondPos := walk_length_pos_of_mem_support_tail
    successor.secondContinuation same.mem_new
  have hleftSum := left.paths.firstRail_length_add_secondRail_length_le_two
  have hrightSum := continuation_length_sum_le_two (successor := successor)
  exact ⟨by omega, hleftTwo, by omega, by omega⟩

private theorem firstSecond_center_lengths
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support
      successor.secondContinuation.support.tail)
    (hcenter :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∈
        successor.secondContinuation.support.tail) :
    0 < left.paths.firstRail.length ∧
      successor.firstContinuation.length = 0 ∧
      successor.secondContinuation.length = 2 := by
  have hne : cross.face ≠
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) :=
    (firstSecondActual cross).toAdjacentDualTriangle.leftCenter_adj_third.ne.symm
  have hrightTwo := length_eq_two_of_two_distinct_mem_tail
    successor.secondContinuation successor.secondContinuation_isPath
    (secondContinuation_length_le_two (successor := successor))
    cross.mem_new hcenter hne
  have hleftPos := walk_length_pos_of_mem_support_of_ne_end
    left.paths.firstRail cross.mem_old
    (firstSecondActual cross).toAdjacentDualTriangle.third_ne_before
  have hrightSum := continuation_length_sum_le_two (successor := successor)
  exact ⟨hleftPos, by omega, hrightTwo⟩

private theorem secondFirst_center_lengths
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support
      successor.firstContinuation.support.tail)
    (hcenter :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∈
        successor.firstContinuation.support.tail) :
    0 < left.paths.secondRail.length ∧
      successor.firstContinuation.length = 2 ∧
      successor.secondContinuation.length = 0 := by
  have hne : cross.face ≠
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) :=
    (secondFirstActual cross).toAdjacentDualTriangle.leftCenter_adj_third.ne.symm
  have hrightTwo := length_eq_two_of_two_distinct_mem_tail
    successor.firstContinuation successor.firstContinuation_isPath
    (firstContinuation_length_le_two (successor := successor))
    cross.mem_new hcenter hne
  have hleftPos := walk_length_pos_of_mem_support_of_ne_end
    left.paths.secondRail cross.mem_old
    (secondFirstActual cross).toAdjacentDualTriangle.third_ne_after
  have hrightSum := continuation_length_sum_le_two (successor := successor)
  exact ⟨hleftPos, hrightTwo, by omega⟩

/-- Provenance-preserving, length-classified form of the adjacent append.
Every residual carries the original cross witness and its forced finite shape. -/
inductive SelectedLocalRailAppendLengthResolvedOutcome
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) : Type (u + 1)
  | straight
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace leftPlacement leftIncomingBefore)
        (selectedPlacementSideFace leftPlacement leftIncomingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter))
  | swapped
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace leftPlacement leftIncomingBefore)
        (selectedPlacementSideFace leftPlacement leftIncomingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore))
  | firstSecondSameFirst
      (cross : SelectedRailSupportCollision (web := web)
        left.paths.firstRail.support successor.secondContinuation.support.tail)
      (same : SelectedRailSupportCollision (web := web)
        left.paths.firstRail.support successor.firstContinuation.support.tail)
      (lengths : left.paths.firstRail.length = 2 ∧
        left.paths.secondRail.length = 0 ∧
        successor.firstContinuation.length = 1 ∧
        successor.secondContinuation.length = 1)
  | firstSecondSameSecond
      (cross : SelectedRailSupportCollision (web := web)
        left.paths.firstRail.support successor.secondContinuation.support.tail)
      (same : SelectedRailSupportCollision (web := web)
        left.paths.secondRail.support successor.secondContinuation.support.tail)
      (lengths : left.paths.firstRail.length = 1 ∧
        left.paths.secondRail.length = 1 ∧
        successor.firstContinuation.length = 0 ∧
        successor.secondContinuation.length = 2)
  | firstSecondCenter
      (cross : SelectedRailSupportCollision (web := web)
        left.paths.firstRail.support successor.secondContinuation.support.tail)
      (center :
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center) ∈ successor.secondContinuation.support.tail)
      (lengths : 0 < left.paths.firstRail.length ∧
        successor.firstContinuation.length = 0 ∧
        successor.secondContinuation.length = 2)
  | secondFirstSameFirst
      (cross : SelectedRailSupportCollision (web := web)
        left.paths.secondRail.support successor.firstContinuation.support.tail)
      (same : SelectedRailSupportCollision (web := web)
        left.paths.firstRail.support successor.firstContinuation.support.tail)
      (lengths : left.paths.firstRail.length = 1 ∧
        left.paths.secondRail.length = 1 ∧
        successor.firstContinuation.length = 2 ∧
        successor.secondContinuation.length = 0)
  | secondFirstSameSecond
      (cross : SelectedRailSupportCollision (web := web)
        left.paths.secondRail.support successor.firstContinuation.support.tail)
      (same : SelectedRailSupportCollision (web := web)
        left.paths.secondRail.support successor.secondContinuation.support.tail)
      (lengths : left.paths.firstRail.length = 0 ∧
        left.paths.secondRail.length = 2 ∧
        successor.firstContinuation.length = 1 ∧
        successor.secondContinuation.length = 1)
  | secondFirstCenter
      (cross : SelectedRailSupportCollision (web := web)
        left.paths.secondRail.support successor.firstContinuation.support.tail)
      (center :
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center) ∈ successor.firstContinuation.support.tail)
      (lengths : 0 < left.paths.secondRail.length ∧
        successor.firstContinuation.length = 2 ∧
        successor.secondContinuation.length = 0)

/-- **L1 length-resolved adjacent classifier.** Centre bridging removes the
bare lone-cross outcome; every remaining branch carries its exact finite
length shape and the witnesses which force it. -/
noncomputable def classifyLocalSuccessorAppendLengthResolved
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) :
    SelectedLocalRailAppendLengthResolvedOutcome successor left :=
  match classifyLocalSuccessorAppendResolved successor left with
  | .straight assembly => .straight assembly
  | .swapped assembly => .swapped assembly
  | .singleFirstSecond cross _ =>
      match classifySingleFirstSecondCenterBridge cross with
      | .assembly value => .swapped value
      | .meetsOldSecond same =>
          .firstSecondSameSecond cross same
            (firstSecond_sameSecond_lengths cross same)
      | .meetsNewFirst same =>
          .firstSecondSameFirst cross same
            (firstSecond_sameFirst_lengths cross same)
      | .containsLeftCenter center =>
          .firstSecondCenter cross center
            (firstSecond_center_lengths cross center)
  | .singleSecondFirst cross _ =>
      match classifySingleSecondFirstCenterBridge cross with
      | .assembly value => .swapped value
      | .meetsOldFirst same =>
          .secondFirstSameFirst cross same
            (secondFirst_sameFirst_lengths cross same)
      | .meetsNewSecond same =>
          .secondFirstSameSecond cross same
            (secondFirst_sameSecond_lengths cross same)
      | .containsLeftCenter center =>
          .secondFirstCenter cross center
            (secondFirst_center_lengths cross center)

end SelectedSourceLocalRailAssembly

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
