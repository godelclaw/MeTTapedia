import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendResidueReroute

/-!
# L1: reroute the two previous-centre append residues

The final finite append residues occur when a length-two successor rail
revisits the previous Cell-3 centre.  Its other tail face is the original
cross collision.  If the cross face is the outgoing endpoint, truncate the
old crossed rail there and send the unmatched rail across the complete centre
bridge.  If the centre is the outgoing endpoint, replace the offending
two-edge successor segment by the literal direct flank-to-centre edge.

Both rail orientations are implemented and their supports are proved to stay
in the literal adjacent two-cell carrier.  Their sharper track provenance is
also retained: each output uses its named old and endpoint-selected successor
track, apart from the three explicit centre-connector faces.  This file does
not yet package them into the exhaustive adjacent classifier, iterate an
arbitrary corridor, attach either end cap, or close Fable flag L1.
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

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
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

private def leftCenterBridge :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        (selectedPlacementSideFace leftPlacement successor.frame.leftAfter)
        (selectedPlacementSideFace leftPlacement successor.frame.leftBefore) :=
  by
    let _ := left
    exact selectedPlacementCenterBridge leftPlacement successor.frame.leftAfter
      successor.frame.leftBefore

private def afterToCenter :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        (selectedPlacementSideFace leftPlacement successor.frame.leftAfter)
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center)) :=
  by
    let _ := left
    exact selectedPlacementSideToCenter leftPlacement successor.frame.leftAfter

private def rightCenterBridge :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        (selectedPlacementSideFace leftPlacement successor.frame.leftBefore)
        (selectedPlacementSideFace leftPlacement successor.frame.leftAfter) :=
  by
    let _ := left
    exact selectedPlacementCenterBridge leftPlacement successor.frame.leftBefore
      successor.frame.leftAfter

private def beforeToCenter :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        (selectedPlacementSideFace leftPlacement successor.frame.leftBefore)
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center)) :=
  by
    let _ := left
    exact selectedPlacementSideToCenter leftPlacement successor.frame.leftBefore

private theorem mem_adjacentPieces_of_mem_centerResidue_leftCenterBridge
    {face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (hface : face ∈ (leftCenterBridge (successor := successor)
      (left := left)).support) :
    FaceInAdjacentSelectedRailPieces (successor := successor)
      (left := left) face := by
  have hbridge : face = selectedPlacementSideFace leftPlacement
        successor.frame.leftAfter ∨
      face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∨
      face = selectedPlacementSideFace leftPlacement
        successor.frame.leftBefore := by
    simpa only [leftCenterBridge, selectedPlacementCenterBridge,
      SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] using hface
  rcases hbridge with hafter | hcenter | hbefore
  · exact Or.inr (Or.inr (Or.inl (hafter ▸
      left.paths.secondRail.end_mem_support)))
  · exact Or.inl hcenter
  · exact Or.inr (Or.inl (hbefore ▸ left.paths.firstRail.end_mem_support))

private theorem mem_adjacentPieces_of_mem_centerResidue_rightCenterBridge
    {face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (hface : face ∈ (rightCenterBridge (successor := successor)
      (left := left)).support) :
    FaceInAdjacentSelectedRailPieces (successor := successor)
      (left := left) face := by
  have hbridge : face = selectedPlacementSideFace leftPlacement
        successor.frame.leftBefore ∨
      face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∨
      face = selectedPlacementSideFace leftPlacement
        successor.frame.leftAfter := by
    simpa only [rightCenterBridge, selectedPlacementCenterBridge,
      SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] using hface
  rcases hbridge with hbefore | hcenter | hafter
  · exact Or.inr (Or.inl (hbefore ▸ left.paths.firstRail.end_mem_support))
  · exact Or.inl hcenter
  · exact Or.inr (Or.inr (Or.inl (hafter ▸
      left.paths.secondRail.end_mem_support)))

private theorem mem_adjacentPieces_of_mem_afterToCenter
    {face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (hface : face ∈ (afterToCenter (successor := successor)
      (left := left)).support) :
    FaceInAdjacentSelectedRailPieces (successor := successor)
      (left := left) face := by
  have hstep : face = selectedPlacementSideFace leftPlacement
        successor.frame.leftAfter ∨
      face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) := by
    simpa only [afterToCenter, selectedPlacementSideToCenter,
      SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] using hface
  rcases hstep with hafter | hcenter
  · exact Or.inr (Or.inr (Or.inl (hafter ▸
      left.paths.secondRail.end_mem_support)))
  · exact Or.inl hcenter

private theorem mem_adjacentPieces_of_mem_beforeToCenter
    {face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (hface : face ∈ (beforeToCenter (successor := successor)
      (left := left)).support) :
    FaceInAdjacentSelectedRailPieces (successor := successor)
      (left := left) face := by
  have hstep : face = selectedPlacementSideFace leftPlacement
        successor.frame.leftBefore ∨
      face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) := by
    simpa only [beforeToCenter, selectedPlacementSideToCenter,
      SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] using hface
  rcases hstep with hbefore | hcenter
  · exact Or.inr (Or.inl (hbefore ▸ left.paths.firstRail.end_mem_support))
  · exact Or.inl hcenter

private theorem support_tail_eq_nil_of_length_eq_zero
    {F : Type*} {H : SimpleGraph F} {start finish : F}
    (walk : H.Walk start finish) (hlength : walk.length = 0) :
    walk.support.tail = [] := by
  cases walk with
  | nil => rfl
  | cons hadj tail => simp at hlength

/-- The first-to-second previous-centre residue constructs a straight or
endpoint-swapped assembly without a global topological premise. -/
noncomputable def appendFirstSecondCenter
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (center :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∈
        successor.secondContinuation.support.tail)
    (lengths : 0 < left.paths.firstRail.length ∧
      successor.firstContinuation.length = 0 ∧
      successor.secondContinuation.length = 2) :
    Sum (SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace leftPlacement leftIncomingBefore)
        (selectedPlacementSideFace leftPlacement leftIncomingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter))
      (SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace leftPlacement leftIncomingBefore)
        (selectedPlacementSideFace leftPlacement leftIncomingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)) := by
  classical
  let actual :
      SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision
        successor left := ⟨cross.face, Or.inl ⟨cross.mem_old, cross.mem_new⟩⟩
  have hfirstFinish : selectedPlacementSideFace leftPlacement
      successor.frame.leftBefore = selectedPlacementSideFace rightPlacement
        successor.rightOutgoingBefore :=
    SimpleGraph.Walk.eq_of_length_eq_zero lengths.2.1
  by_cases hcrossEnd : cross.face = selectedPlacementSideFace rightPlacement
      successor.rightOutgoingAfter
  · refine Sum.inr ?_
    let firstRail := (left.paths.firstRail.takeUntil cross.face
      cross.mem_old).copy rfl hcrossEnd
    let rawSecond :=
      (left.paths.secondRail.append (leftCenterBridge (successor := successor)
        (left := left))).append successor.firstContinuation
    refine {
      firstRail := firstRail
      secondRail := rawSecond.bypass
      firstRail_isPath := by
        simpa [firstRail] using left.paths.firstRail_isPath.takeUntil cross.mem_old
      secondRail_isPath := rawSecond.bypass_isPath
      firstRail_support_disjoint_secondRail := ?_
    }
    rw [List.disjoint_left]
    intro face hfirst hsecond
    rw [SimpleGraph.Walk.support_copy] at hfirst
    have hfirstOld := left.paths.firstRail.support_takeUntil_subset_support
      cross.mem_old hfirst
    have hraw := rawSecond.support_bypass_subset_support hsecond
    simp only [rawSecond, SimpleGraph.Walk.support_append, List.mem_append] at hraw
    rcases hraw with (hold | hbridge) | hnew
    · exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
        hfirstOld) hold
    · have hbridge' : face =
            (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
              |>.faceAt leftInterior.center) ∨
          face = selectedPlacementSideFace leftPlacement
            successor.frame.leftBefore := by
        simpa only [leftCenterBridge, selectedPlacementCenterBridge,
          SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false]
          using hbridge
      rcases hbridge' with hcenter | hbefore
      · exact (left.paths.firstRail_support_adjacent_center face hfirstOld).ne
          hcenter.symm
      · exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          left.paths.firstRail_isPath cross.mem_old
          actual.toAdjacentDualTriangle.third_ne_before.symm
          (hbefore ▸ hfirst)
    · have htailEmpty : successor.firstContinuation.support.tail = [] :=
        support_tail_eq_nil_of_length_eq_zero successor.firstContinuation
          lengths.2.1
      rw [htailEmpty] at hnew
      exact List.not_mem_nil hnew
  · have hcenterEnd :
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center) =
          selectedPlacementSideFace rightPlacement
            successor.rightOutgoingAfter :=
      (firstSecondCenter_cross_eq_end_or_center_eq_end
        cross center lengths).resolve_left hcrossEnd
    refine Sum.inl ?_
    let firstRail := left.paths.firstRail.copy rfl hfirstFinish
    let rawSecond := left.paths.secondRail.append
      (afterToCenter (successor := successor) (left := left))
    let secondRail := rawSecond.bypass.copy rfl hcenterEnd
    refine {
      firstRail := firstRail
      secondRail := secondRail
      firstRail_isPath := by simpa [firstRail] using left.paths.firstRail_isPath
      secondRail_isPath := by simpa [secondRail] using rawSecond.bypass_isPath
      firstRail_support_disjoint_secondRail := ?_
    }
    rw [List.disjoint_left]
    intro face hfirst hsecond
    rw [SimpleGraph.Walk.support_copy] at hfirst hsecond
    have hraw := rawSecond.support_bypass_subset_support hsecond
    simp only [rawSecond, SimpleGraph.Walk.support_append, List.mem_append] at hraw
    rcases hraw with hold | hstep
    · exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
        hfirst) hold
    · have hcenterFace : face =
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
            |>.faceAt leftInterior.center) := by
        simpa only [afterToCenter, selectedPlacementSideToCenter,
          SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_singleton]
          using hstep
      exact (left.paths.firstRail_support_adjacent_center face hfirst).ne
        hcenterFace.symm

/-- The first-to-second centre-revisit repair stays in the literal adjacent
two-cell carrier. -/
theorem appendFirstSecondCenter_supportContained
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (center :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∈
        successor.secondContinuation.support.tail)
    (lengths : 0 < left.paths.firstRail.length ∧
      successor.firstContinuation.length = 0 ∧
      successor.secondContinuation.length = 2) :
    AssemblySumSupportedByAdjacentSelectedRailPieces (successor := successor)
      (left := left) (appendFirstSecondCenter cross center lengths) := by
  classical
  by_cases hcrossEnd : cross.face =
      selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter
  · simp only [appendFirstSecondCenter, hcrossEnd,
      AssemblySumSupportedByAdjacentSelectedRailPieces,
      AssemblySupportedByAdjacentSelectedRailPieces]
    constructor
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      exact Or.inr (Or.inl
        (left.paths.firstRail.support_takeUntil_subset_support cross.mem_old hface))
    · intro face hface
      let rawSecond :=
        (left.paths.secondRail.append (leftCenterBridge (successor := successor)
          (left := left))).append successor.firstContinuation
      have hraw : face ∈ rawSecond.support :=
        rawSecond.support_bypass_subset_support hface
      simp only [rawSecond, SimpleGraph.Walk.support_append, List.mem_append] at hraw
      rcases hraw with (hold | hbridge) | hnew
      · exact Or.inr (Or.inr (Or.inl hold))
      · exact mem_adjacentPieces_of_mem_centerResidue_leftCenterBridge
          (successor := successor) (left := left) (List.mem_of_mem_tail hbridge)
      · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_tail hnew))))
  · simp only [appendFirstSecondCenter, hcrossEnd,
      AssemblySumSupportedByAdjacentSelectedRailPieces,
      AssemblySupportedByAdjacentSelectedRailPieces]
    constructor
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      exact Or.inr (Or.inl hface)
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      let rawSecond := left.paths.secondRail.append
        (afterToCenter (successor := successor) (left := left))
      have hraw : face ∈ rawSecond.support :=
        rawSecond.support_bypass_subset_support hface
      rw [SimpleGraph.Walk.support_append] at hraw
      rcases List.mem_append.mp hraw with hold | hstep
      · exact Or.inr (Or.inr (Or.inl hold))
      · exact mem_adjacentPieces_of_mem_afterToCenter
          (successor := successor) (left := left) (List.mem_of_mem_tail hstep)

/-- The first-to-second centre-revisit repair preserves the expected rail
tracks modulo the two seam flanks and the displayed Cell-3 centre. -/
theorem appendFirstSecondCenter_trackProvenance
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (center :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∈
        successor.secondContinuation.support.tail)
    (lengths : 0 < left.paths.firstRail.length ∧
      successor.firstContinuation.length = 0 ∧
      successor.secondContinuation.length = 2) :
    AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
      (left := left) (appendFirstSecondCenter cross center lengths) := by
  classical
  by_cases hcrossEnd : cross.face =
      selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter
  · simp only [appendFirstSecondCenter, hcrossEnd,
      AssemblySumSupportedByExpectedSelectedRailTracks,
      FaceInExpectedSelectedRailTrack]
    constructor
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      exact Or.inl
        (left.paths.firstRail.support_takeUntil_subset_support cross.mem_old hface)
    · intro face hface
      let rawSecond :=
        (left.paths.secondRail.append (leftCenterBridge (successor := successor)
          (left := left))).append successor.firstContinuation
      have hraw : face ∈ rawSecond.support :=
        rawSecond.support_bypass_subset_support hface
      simp only [rawSecond, SimpleGraph.Walk.support_append, List.mem_append] at hraw
      rcases hraw with (hold | hbridge) | hnew
      · exact Or.inl hold
      · have hbridge' : face =
            (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
              |>.faceAt leftInterior.center) ∨
          face = selectedPlacementSideFace leftPlacement
            successor.frame.leftBefore := by
          simpa only [leftCenterBridge, selectedPlacementCenterBridge,
            SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_cons,
            List.mem_singleton, List.not_mem_nil, or_false] using hbridge
        rcases hbridge' with hcenter | hbefore
        · exact Or.inr (Or.inr (Or.inl hcenter))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hbefore)))
      · exact Or.inr (Or.inl (List.mem_of_mem_tail hnew))
  · simp only [appendFirstSecondCenter, hcrossEnd,
      AssemblySumSupportedByExpectedSelectedRailTracks,
      FaceInExpectedSelectedRailTrack]
    constructor
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      exact Or.inl hface
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      let rawSecond := left.paths.secondRail.append
        (afterToCenter (successor := successor) (left := left))
      have hraw : face ∈ rawSecond.support :=
        rawSecond.support_bypass_subset_support hface
      rw [SimpleGraph.Walk.support_append] at hraw
      rcases List.mem_append.mp hraw with hold | hstep
      · exact Or.inl hold
      · have hcenterFace : face =
            (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
              |>.faceAt leftInterior.center) := by
          simpa only [afterToCenter, selectedPlacementSideToCenter,
            SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil, List.tail_cons,
            List.mem_singleton] using hstep
        exact Or.inr (Or.inr (Or.inl hcenterFace))

/-- Rail-exchanged construction of the second-to-first centre residue. -/
noncomputable def appendSecondFirstCenter
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (center :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∈
        successor.firstContinuation.support.tail)
    (lengths : 0 < left.paths.secondRail.length ∧
      successor.firstContinuation.length = 2 ∧
      successor.secondContinuation.length = 0) :
    Sum (SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace leftPlacement leftIncomingBefore)
        (selectedPlacementSideFace leftPlacement leftIncomingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter))
      (SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace leftPlacement leftIncomingBefore)
        (selectedPlacementSideFace leftPlacement leftIncomingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)) := by
  classical
  let actual :
      SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision
        successor left := ⟨cross.face, Or.inr ⟨cross.mem_old, cross.mem_new⟩⟩
  have hsecondFinish : selectedPlacementSideFace leftPlacement
      successor.frame.leftAfter = selectedPlacementSideFace rightPlacement
        successor.rightOutgoingAfter :=
    SimpleGraph.Walk.eq_of_length_eq_zero lengths.2.2
  by_cases hcrossEnd : cross.face = selectedPlacementSideFace rightPlacement
      successor.rightOutgoingBefore
  · refine Sum.inr ?_
    let rawFirst :=
      (left.paths.firstRail.append (rightCenterBridge (successor := successor)
        (left := left))).append successor.secondContinuation
    let secondRail := (left.paths.secondRail.takeUntil cross.face
      cross.mem_old).copy rfl hcrossEnd
    refine {
      firstRail := rawFirst.bypass
      secondRail := secondRail
      firstRail_isPath := rawFirst.bypass_isPath
      secondRail_isPath := by
        simpa [secondRail] using left.paths.secondRail_isPath.takeUntil cross.mem_old
      firstRail_support_disjoint_secondRail := ?_
    }
    rw [List.disjoint_left]
    intro face hfirst hsecond
    rw [SimpleGraph.Walk.support_copy] at hsecond
    have hsecondOld := left.paths.secondRail.support_takeUntil_subset_support
      cross.mem_old hsecond
    have hraw := rawFirst.support_bypass_subset_support hfirst
    simp only [rawFirst, SimpleGraph.Walk.support_append, List.mem_append] at hraw
    rcases hraw with (hold | hbridge) | hnew
    · exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
        hold) hsecondOld
    · have hbridge' : face =
            (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
              |>.faceAt leftInterior.center) ∨
          face = selectedPlacementSideFace leftPlacement
            successor.frame.leftAfter := by
        simpa only [rightCenterBridge, selectedPlacementCenterBridge,
          SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false]
          using hbridge
      rcases hbridge' with hcenter | hafter
      · exact (left.paths.secondRail_support_adjacent_center face hsecondOld).ne
          hcenter.symm
      · exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          left.paths.secondRail_isPath cross.mem_old
          actual.toAdjacentDualTriangle.third_ne_after.symm
          (hafter ▸ hsecond)
    · have htailEmpty : successor.secondContinuation.support.tail = [] :=
        support_tail_eq_nil_of_length_eq_zero successor.secondContinuation
          lengths.2.2
      rw [htailEmpty] at hnew
      exact List.not_mem_nil hnew
  · have hcenterEnd :
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          |>.faceAt leftInterior.center) =
          selectedPlacementSideFace rightPlacement
            successor.rightOutgoingBefore :=
      (secondFirstCenter_cross_eq_end_or_center_eq_end
        cross center lengths).resolve_left hcrossEnd
    refine Sum.inl ?_
    let rawFirst := left.paths.firstRail.append
      (beforeToCenter (successor := successor) (left := left))
    let firstRail := rawFirst.bypass.copy rfl hcenterEnd
    let secondRail := left.paths.secondRail.copy rfl hsecondFinish
    refine {
      firstRail := firstRail
      secondRail := secondRail
      firstRail_isPath := by simpa [firstRail] using rawFirst.bypass_isPath
      secondRail_isPath := by
        simpa [secondRail] using left.paths.secondRail_isPath
      firstRail_support_disjoint_secondRail := ?_
    }
    rw [List.disjoint_left]
    intro face hfirst hsecond
    rw [SimpleGraph.Walk.support_copy] at hfirst hsecond
    have hraw := rawFirst.support_bypass_subset_support hfirst
    simp only [rawFirst, SimpleGraph.Walk.support_append, List.mem_append] at hraw
    rcases hraw with hold | hstep
    · exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
        hold) hsecond
    · have hcenterFace : face =
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
            |>.faceAt leftInterior.center) := by
        simpa only [beforeToCenter, selectedPlacementSideToCenter,
          SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_singleton]
          using hstep
      exact (left.paths.secondRail_support_adjacent_center face hsecond).ne
        hcenterFace.symm

/-- The rail-exchanged centre-revisit repair has the same provenance. -/
theorem appendSecondFirstCenter_supportContained
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (center :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∈
        successor.firstContinuation.support.tail)
    (lengths : 0 < left.paths.secondRail.length ∧
      successor.firstContinuation.length = 2 ∧
      successor.secondContinuation.length = 0) :
    AssemblySumSupportedByAdjacentSelectedRailPieces (successor := successor)
      (left := left) (appendSecondFirstCenter cross center lengths) := by
  classical
  by_cases hcrossEnd : cross.face =
      selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore
  · simp only [appendSecondFirstCenter, hcrossEnd,
      AssemblySumSupportedByAdjacentSelectedRailPieces,
      AssemblySupportedByAdjacentSelectedRailPieces]
    constructor
    · intro face hface
      let rawFirst :=
        (left.paths.firstRail.append (rightCenterBridge (successor := successor)
          (left := left))).append successor.secondContinuation
      have hraw : face ∈ rawFirst.support :=
        rawFirst.support_bypass_subset_support hface
      simp only [rawFirst, SimpleGraph.Walk.support_append, List.mem_append] at hraw
      rcases hraw with (hold | hbridge) | hnew
      · exact Or.inr (Or.inl hold)
      · exact mem_adjacentPieces_of_mem_centerResidue_rightCenterBridge
          (successor := successor) (left := left) (List.mem_of_mem_tail hbridge)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (List.mem_of_mem_tail hnew))))
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      exact Or.inr (Or.inr (Or.inl
        (left.paths.secondRail.support_takeUntil_subset_support cross.mem_old hface)))
  · simp only [appendSecondFirstCenter, hcrossEnd,
      AssemblySumSupportedByAdjacentSelectedRailPieces,
      AssemblySupportedByAdjacentSelectedRailPieces]
    constructor
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      let rawFirst := left.paths.firstRail.append
        (beforeToCenter (successor := successor) (left := left))
      have hraw : face ∈ rawFirst.support :=
        rawFirst.support_bypass_subset_support hface
      rw [SimpleGraph.Walk.support_append] at hraw
      rcases List.mem_append.mp hraw with hold | hstep
      · exact Or.inr (Or.inl hold)
      · exact mem_adjacentPieces_of_mem_beforeToCenter
          (successor := successor) (left := left) (List.mem_of_mem_tail hstep)
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      exact Or.inr (Or.inr (Or.inl hface))

/-- The symmetric centre-revisit repair has the same track-sensitive
provenance. -/
theorem appendSecondFirstCenter_trackProvenance
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (center :
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center) ∈
        successor.firstContinuation.support.tail)
    (lengths : 0 < left.paths.secondRail.length ∧
      successor.firstContinuation.length = 2 ∧
      successor.secondContinuation.length = 0) :
    AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
      (left := left) (appendSecondFirstCenter cross center lengths) := by
  classical
  by_cases hcrossEnd : cross.face =
      selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore
  · simp only [appendSecondFirstCenter, hcrossEnd,
      AssemblySumSupportedByExpectedSelectedRailTracks,
      FaceInExpectedSelectedRailTrack]
    constructor
    · intro face hface
      let rawFirst :=
        (left.paths.firstRail.append (rightCenterBridge (successor := successor)
          (left := left))).append successor.secondContinuation
      have hraw : face ∈ rawFirst.support :=
        rawFirst.support_bypass_subset_support hface
      simp only [rawFirst, SimpleGraph.Walk.support_append, List.mem_append] at hraw
      rcases hraw with (hold | hbridge) | hnew
      · exact Or.inl hold
      · have hbridge' : face =
            (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
              |>.faceAt leftInterior.center) ∨
          face = selectedPlacementSideFace leftPlacement
            successor.frame.leftAfter := by
          simpa only [rightCenterBridge, selectedPlacementCenterBridge,
            SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_cons,
            List.mem_singleton, List.not_mem_nil, or_false] using hbridge
        rcases hbridge' with hcenter | hafter
        · exact Or.inr (Or.inr (Or.inl hcenter))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hafter)))
      · exact Or.inr (Or.inl (List.mem_of_mem_tail hnew))
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      exact Or.inl
        (left.paths.secondRail.support_takeUntil_subset_support cross.mem_old hface)
  · simp only [appendSecondFirstCenter, hcrossEnd,
      AssemblySumSupportedByExpectedSelectedRailTracks,
      FaceInExpectedSelectedRailTrack]
    constructor
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      let rawFirst := left.paths.firstRail.append
        (beforeToCenter (successor := successor) (left := left))
      have hraw : face ∈ rawFirst.support :=
        rawFirst.support_bypass_subset_support hface
      rw [SimpleGraph.Walk.support_append] at hraw
      rcases List.mem_append.mp hraw with hold | hstep
      · exact Or.inl hold
      · have hcenterFace : face =
            (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
              |>.faceAt leftInterior.center) := by
          simpa only [beforeToCenter, selectedPlacementSideToCenter,
            SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil, List.tail_cons,
            List.mem_singleton] using hstep
        exact Or.inr (Or.inr (Or.inl hcenterFace))
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      exact Or.inl hface

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
