import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendResidueCoordinates
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailCenterEdgeReceipt

/-!
# L1: construct the first length-and-coordinate append residue

The `firstSecondSameFirst` residue has old lengths `2+0` and successor
lengths `1+1`.  Its endpoint classification leaves two cases.  If the
same-track collision is the old first start, that rail contracts to the
stationary path.  If the cross-track collision is the old first start, the
crossed rail contracts instead and the unmatched rail uses the literal
two-edge walk through the previous Cell-3 centre.

This file constructs both alternatives and proves the resulting rails simple
and mutually support-disjoint.  It also proves their rail-exchanged and
seam-reversed forms, discharging four of the six oriented finite residues,
and proves that every resulting support stays in the literal adjacent
two-cell carrier.  The four repairs now also retain track-sensitive
provenance: each output uses its named old rail and endpoint-selected
successor rail, apart from the three explicitly named centre-connector faces.
The two centre-revisit residues remain; this file does not yet give the full
adjacent classifier, iterate a corridor, attach end caps, or close Fable flag
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

/-- The finite source carrier from which every adjacent repair is assembled:
the previous centre itself, either old local rail, or either successor rail.
It lives beside the repair constructors so their private bridge walks can
export provenance without exposing those implementation details. -/
def FaceInAdjacentSelectedRailPieces
    (face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))) : Prop :=
  face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      |>.faceAt leftInterior.center) ∨
    face ∈ left.paths.firstRail.support ∨
    face ∈ left.paths.secondRail.support ∨
    face ∈ successor.firstContinuation.support ∨
    face ∈ successor.secondContinuation.support

/-- Both supports of a repaired local assembly stay in the five-piece
adjacent source carrier. -/
def AssemblySupportedByAdjacentSelectedRailPieces
    {firstFinish secondFinish :
      AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter)
      firstFinish secondFinish) : Prop :=
  (∀ face ∈ assembly.firstRail.support,
      FaceInAdjacentSelectedRailPieces (successor := successor)
        (left := left) face) ∧
    ∀ face ∈ assembly.secondRail.support,
      FaceInAdjacentSelectedRailPieces (successor := successor)
        (left := left) face

/-- Provenance for a repair which may preserve or exchange its outgoing
endpoint labels. -/
def AssemblySumSupportedByAdjacentSelectedRailPieces
    (result :
      Sum (SelectedSourceLocalRailAssembly (web := web)
          (selectedPlacementSideFace leftPlacement leftIncomingBefore)
          (selectedPlacementSideFace leftPlacement leftIncomingAfter)
          (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)
          (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter))
        (SelectedSourceLocalRailAssembly (web := web)
          (selectedPlacementSideFace leftPlacement leftIncomingBefore)
          (selectedPlacementSideFace leftPlacement leftIncomingAfter)
          (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
          (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore))) : Prop :=
  match result with
  | .inl assembly =>
      AssemblySupportedByAdjacentSelectedRailPieces (successor := successor)
        (left := left) assembly
  | .inr assembly =>
      AssemblySupportedByAdjacentSelectedRailPieces (successor := successor)
        (left := left) assembly

/-- A face stays on one named rail track, apart from the three literal
connector faces of the displayed Cell-3 bridge.  Naming the two seam flanks
separately is essential: a centre bridge may touch the opposite old rail at
its endpoint without using any interior face of that rail. -/
def FaceInExpectedSelectedRailTrack
    (oldSupport newSupport : List
      (AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))))
    (face : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))) : Prop :=
  face ∈ oldSupport ∨ face ∈ newSupport ∨
    face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      |>.faceAt leftInterior.center) ∨
    face = selectedPlacementSideFace leftPlacement successor.frame.leftBefore ∨
    face = selectedPlacementSideFace leftPlacement successor.frame.leftAfter

/-- Track-sensitive provenance for a repair which may preserve or exchange
its outgoing endpoint labels.  Unlike the five-piece envelope above, this
records which old rail and which successor rail can occur in each output. -/
def AssemblySumSupportedByExpectedSelectedRailTracks
    (result :
      Sum (SelectedSourceLocalRailAssembly (web := web)
          (selectedPlacementSideFace leftPlacement leftIncomingBefore)
          (selectedPlacementSideFace leftPlacement leftIncomingAfter)
          (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)
          (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter))
        (SelectedSourceLocalRailAssembly (web := web)
          (selectedPlacementSideFace leftPlacement leftIncomingBefore)
          (selectedPlacementSideFace leftPlacement leftIncomingAfter)
          (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
          (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore))) : Prop :=
  match result with
  | .inl assembly =>
      (∀ face ∈ assembly.firstRail.support,
          FaceInExpectedSelectedRailTrack (corridor := corridor)
            (leftInterior := leftInterior)
            (leftPlacement := leftPlacement) (successor := successor)
            left.paths.firstRail.support
            successor.firstContinuation.support face) ∧
        ∀ face ∈ assembly.secondRail.support,
          FaceInExpectedSelectedRailTrack (corridor := corridor)
            (leftInterior := leftInterior)
            (leftPlacement := leftPlacement) (successor := successor)
            left.paths.secondRail.support
            successor.secondContinuation.support face
  | .inr assembly =>
      (∀ face ∈ assembly.firstRail.support,
          FaceInExpectedSelectedRailTrack (corridor := corridor)
            (leftInterior := leftInterior)
            (leftPlacement := leftPlacement) (successor := successor)
            left.paths.firstRail.support
            successor.secondContinuation.support face) ∧
        ∀ face ∈ assembly.secondRail.support,
          FaceInExpectedSelectedRailTrack (corridor := corridor)
            (leftInterior := leftInterior)
            (leftPlacement := leftPlacement) (successor := successor)
            left.paths.secondRail.support
            successor.firstContinuation.support face

private theorem eq_end_of_mem_support_tail_of_length_le_one
    {F : Type*} {H : SimpleGraph F} {start finish face : F}
    (walk : H.Walk start finish) (hlength : walk.length ≤ 1)
    (hface : face ∈ walk.support.tail) : face = finish := by
  cases walk with
  | nil => simp at hface
  | @cons next _ _ hadj tail =>
      cases tail with
      | nil => simpa using hface
      | @cons last _ _ hnext rest =>
          simp only [SimpleGraph.Walk.length_cons] at hlength
          omega

private theorem eq_start_of_mem_support_of_length_le_one_of_ne_end
    {F : Type*} {H : SimpleGraph F} {start finish face : F}
    (walk : H.Walk start finish) (hlength : walk.length ≤ 1)
    (hface : face ∈ walk.support) (hne : face ≠ finish) : face = start := by
  cases walk with
  | nil => simpa using hface
  | @cons next _ _ hadj tail =>
      cases tail with
      | nil => simpa [hne] using hface
      | @cons last _ _ hnext rest =>
          simp only [SimpleGraph.Walk.length_cons] at hlength
          omega

private theorem support_tail_eq_nil_of_length_eq_zero
    {F : Type*} {H : SimpleGraph F} {start finish : F}
    (walk : H.Walk start finish) (hlength : walk.length = 0) :
    walk.support.tail = [] := by
  cases walk with
  | nil => rfl
  | cons hadj tail => simp at hlength

private def leftCenterBridge :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        (selectedPlacementSideFace leftPlacement successor.frame.leftAfter)
        (selectedPlacementSideFace leftPlacement successor.frame.leftBefore) :=
  by
    let _ := left
    exact selectedPlacementCenterBridge leftPlacement successor.frame.leftAfter
      successor.frame.leftBefore

/-- The left-to-right bridge introduces only the previous Cell-3 centre;
its two flank endpoints already belong to the old local rails. -/
theorem mem_adjacentSelectedRailPieces_of_mem_leftCenterBridge_support
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

/-- The `firstSecondSameFirst` residue always constructs either the straight
or the endpoint-swapped two-cell assembly. -/
noncomputable def appendFirstSecondSameFirst
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.firstContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 2 ∧
      left.paths.secondRail.length = 0 ∧
      successor.firstContinuation.length = 1 ∧
      successor.secondContinuation.length = 1) :
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
  have hcrossEnd : cross.face = selectedPlacementSideFace rightPlacement
      successor.rightOutgoingAfter :=
    eq_end_of_mem_support_tail_of_length_le_one successor.secondContinuation
      (by omega) cross.mem_new
  have hsameEnd : same.face = selectedPlacementSideFace rightPlacement
      successor.rightOutgoingBefore :=
    eq_end_of_mem_support_tail_of_length_le_one successor.firstContinuation
      (by omega) same.mem_new
  have hsecondStart : selectedPlacementSideFace leftPlacement leftIncomingAfter =
      selectedPlacementSideFace leftPlacement successor.frame.leftAfter :=
    SimpleGraph.Walk.eq_of_length_eq_zero lengths.2.1
  have hcrossNeSame : cross.face ≠ same.face := by
    intro heq
    exact (List.disjoint_left.mp
      successor.firstContinuation_support_disjoint_secondContinuation
        (List.mem_of_mem_tail same.mem_new))
      (List.mem_of_mem_tail (heq ▸ cross.mem_new))
  by_cases hcrossStart : cross.face =
      selectedPlacementSideFace leftPlacement leftIncomingBefore
  · refine Sum.inr ?_
    let rawSecond :=
      (left.paths.secondRail.append (leftCenterBridge (successor := successor)
        (left := left))).append successor.firstContinuation
    refine {
      firstRail := SimpleGraph.Walk.nil.copy rfl (hcrossStart.symm.trans hcrossEnd)
      secondRail := rawSecond.bypass
      firstRail_isPath := by simp
      secondRail_isPath := rawSecond.bypass_isPath
      firstRail_support_disjoint_secondRail := ?_
    }
    rw [List.disjoint_left]
    intro face hfirst hsecond
    have hfirstEq : face = cross.face := by simpa [hcrossStart] using hfirst
    have hrawCross : cross.face ∈ rawSecond.support :=
      hfirstEq ▸ rawSecond.support_bypass_subset_support hsecond
    simp only [rawSecond, SimpleGraph.Walk.support_append, List.mem_append] at hrawCross
    rcases hrawCross with (hold | hbridge) | hnew
    · exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
        cross.mem_old) hold
    · have hbridge' : cross.face =
            (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
              |>.faceAt leftInterior.center) ∨
          cross.face = selectedPlacementSideFace leftPlacement
            successor.frame.leftBefore := by
        simpa only [leftCenterBridge, selectedPlacementCenterBridge,
          SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false]
          using hbridge
      by_cases hcenter : cross.face =
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
            |>.faceAt leftInterior.center)
      · exact (left.paths.firstRail_support_adjacent_center cross.face
          cross.mem_old).ne hcenter.symm
      · have hbefore : cross.face = selectedPlacementSideFace leftPlacement
            successor.frame.leftBefore := by
          exact hbridge'.resolve_left hcenter
        have hcrossFull : cross.face ∈
            successor.secondContinuation.support :=
          List.mem_of_mem_tail cross.mem_new
        have hbeforeFull : selectedPlacementSideFace leftPlacement
            successor.frame.leftBefore ∈ successor.firstContinuation.support :=
          successor.firstContinuation.start_mem_support
        have hcrossFirst : cross.face ∈
            successor.firstContinuation.support := by
          simpa only [hbefore] using hbeforeFull
        exact (List.disjoint_left.mp
          successor.firstContinuation_support_disjoint_secondContinuation
            hcrossFirst) hcrossFull
    · exact (List.disjoint_left.mp
        successor.firstContinuation_support_disjoint_secondContinuation
          (List.mem_of_mem_tail hnew)) (List.mem_of_mem_tail cross.mem_new)
  · have hsameStart : same.face =
        selectedPlacementSideFace leftPlacement leftIncomingBefore :=
      (firstSecondSameFirst_cross_eq_start_or_same_eq_start
        cross same lengths).resolve_left hcrossStart
    refine Sum.inl ?_
    let secondRail := successor.secondContinuation.copy hsecondStart.symm rfl
    refine {
      firstRail := SimpleGraph.Walk.nil.copy rfl (hsameStart.symm.trans hsameEnd)
      secondRail := secondRail
      firstRail_isPath := by simp
      secondRail_isPath := by
        simpa [secondRail] using successor.secondContinuation_isPath
      firstRail_support_disjoint_secondRail := ?_
    }
    rw [List.disjoint_left]
    intro face hfirst hsecond
    have hfirstEq : face = same.face := by simpa [hsameStart] using hfirst
    have hsecond' : same.face ∈ successor.secondContinuation.support := by
      rw [SimpleGraph.Walk.support_copy] at hsecond
      simpa only [hfirstEq] using hsecond
    by_cases hstart : same.face = selectedPlacementSideFace leftPlacement
        successor.frame.leftAfter
    · exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
        same.mem_old) (by
          simpa only [hstart] using left.paths.secondRail.end_mem_support)
    · have htail : same.face ∈ successor.secondContinuation.support.tail := by
        rw [← successor.secondContinuation.cons_tail_support] at hsecond'
        simpa only [List.mem_cons, hstart, false_or] using hsecond'
      have htailEnd := eq_end_of_mem_support_tail_of_length_le_one
        successor.secondContinuation (by omega) htail
      exact hcrossNeSame (hcrossEnd.trans htailEnd.symm)

/-- The first stationary/centre-bridge residue introduces no face outside
the literal adjacent two-cell carrier. -/
theorem appendFirstSecondSameFirst_supportContained
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.firstContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 2 ∧
      left.paths.secondRail.length = 0 ∧
      successor.firstContinuation.length = 1 ∧
      successor.secondContinuation.length = 1) :
    AssemblySumSupportedByAdjacentSelectedRailPieces (successor := successor)
      (left := left) (appendFirstSecondSameFirst cross same lengths) := by
  classical
  by_cases hcrossStart : cross.face =
      selectedPlacementSideFace leftPlacement leftIncomingBefore
  · simp only [appendFirstSecondSameFirst, hcrossStart,
      AssemblySumSupportedByAdjacentSelectedRailPieces,
      AssemblySupportedByAdjacentSelectedRailPieces]
    constructor
    · intro face hface
      have hfaceEq : face = cross.face := by simpa [hcrossStart] using hface
      exact Or.inr (Or.inl (hfaceEq ▸ cross.mem_old))
    · intro face hface
      let rawSecond :=
        (left.paths.secondRail.append (leftCenterBridge (successor := successor)
          (left := left))).append successor.firstContinuation
      have hraw : face ∈ rawSecond.support :=
        rawSecond.support_bypass_subset_support hface
      simp only [rawSecond, SimpleGraph.Walk.support_append, List.mem_append] at hraw
      rcases hraw with (hold | hbridge) | hnew
      · exact Or.inr (Or.inr (Or.inl hold))
      · exact mem_adjacentSelectedRailPieces_of_mem_leftCenterBridge_support
          (successor := successor) (left := left)
          (List.mem_of_mem_tail hbridge)
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          (List.mem_of_mem_tail hnew))))
  · simp only [appendFirstSecondSameFirst, hcrossStart,
      AssemblySumSupportedByAdjacentSelectedRailPieces,
      AssemblySupportedByAdjacentSelectedRailPieces]
    constructor
    · intro face hface
      have hsameStart : same.face =
          selectedPlacementSideFace leftPlacement leftIncomingBefore :=
        (firstSecondSameFirst_cross_eq_start_or_same_eq_start
          cross same lengths).resolve_left hcrossStart
      have hfaceEq : face = same.face := by simpa [hsameStart] using hface
      exact Or.inr (Or.inl (hfaceEq ▸ same.mem_old))
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      exact Or.inr (Or.inr (Or.inr (Or.inr hface)))

/-- The first stationary residue preserves the two named rail tracks, with
the successor tracks exchanged exactly when the endpoint order is exchanged. -/
theorem appendFirstSecondSameFirst_trackProvenance
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.firstContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 2 ∧
      left.paths.secondRail.length = 0 ∧
      successor.firstContinuation.length = 1 ∧
      successor.secondContinuation.length = 1) :
    AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
      (left := left) (appendFirstSecondSameFirst cross same lengths) := by
  classical
  by_cases hcrossStart : cross.face =
      selectedPlacementSideFace leftPlacement leftIncomingBefore
  · simp only [appendFirstSecondSameFirst, hcrossStart,
      AssemblySumSupportedByExpectedSelectedRailTracks,
      FaceInExpectedSelectedRailTrack]
    constructor
    · intro face hface
      have hfaceEq : face = cross.face := by simpa [hcrossStart] using hface
      exact Or.inl (hfaceEq ▸ cross.mem_old)
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
  · simp only [appendFirstSecondSameFirst, hcrossStart,
      AssemblySumSupportedByExpectedSelectedRailTracks,
      FaceInExpectedSelectedRailTrack]
    constructor
    · intro face hface
      have hsameStart : same.face =
          selectedPlacementSideFace leftPlacement leftIncomingBefore :=
        (firstSecondSameFirst_cross_eq_start_or_same_eq_start
          cross same lengths).resolve_left hcrossStart
      have hfaceEq : face = same.face := by simpa [hsameStart] using hface
      exact Or.inl (hfaceEq ▸ same.mem_old)
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      exact Or.inr (Or.inl hface)

private def rightCenterBridge :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        (selectedPlacementSideFace leftPlacement successor.frame.leftBefore)
        (selectedPlacementSideFace leftPlacement successor.frame.leftAfter) :=
  by
    let _ := left
    exact selectedPlacementCenterBridge leftPlacement successor.frame.leftBefore
      successor.frame.leftAfter

/-- The right-to-left bridge has the same finite source provenance. -/
theorem mem_adjacentSelectedRailPieces_of_mem_rightCenterBridge_support
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

/-- Symmetric construction for the `secondFirstSameSecond` residue. -/
noncomputable def appendSecondFirstSameSecond
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.secondContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 0 ∧
      left.paths.secondRail.length = 2 ∧
      successor.firstContinuation.length = 1 ∧
      successor.secondContinuation.length = 1) :
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
  have hcrossEnd : cross.face = selectedPlacementSideFace rightPlacement
      successor.rightOutgoingBefore :=
    eq_end_of_mem_support_tail_of_length_le_one successor.firstContinuation
      (by omega) cross.mem_new
  have hsameEnd : same.face = selectedPlacementSideFace rightPlacement
      successor.rightOutgoingAfter :=
    eq_end_of_mem_support_tail_of_length_le_one successor.secondContinuation
      (by omega) same.mem_new
  have hfirstStart : selectedPlacementSideFace leftPlacement leftIncomingBefore =
      selectedPlacementSideFace leftPlacement successor.frame.leftBefore :=
    SimpleGraph.Walk.eq_of_length_eq_zero lengths.1
  have hcrossNeSame : cross.face ≠ same.face := by
    intro heq
    exact (List.disjoint_left.mp
      successor.firstContinuation_support_disjoint_secondContinuation
        (List.mem_of_mem_tail cross.mem_new))
      (List.mem_of_mem_tail (heq ▸ same.mem_new))
  by_cases hcrossStart : cross.face =
      selectedPlacementSideFace leftPlacement leftIncomingAfter
  · refine Sum.inr ?_
    let rawFirst :=
      (left.paths.firstRail.append (rightCenterBridge (successor := successor)
        (left := left))).append successor.secondContinuation
    refine {
      firstRail := rawFirst.bypass
      secondRail := SimpleGraph.Walk.nil.copy rfl
        (hcrossStart.symm.trans hcrossEnd)
      firstRail_isPath := rawFirst.bypass_isPath
      secondRail_isPath := by simp
      firstRail_support_disjoint_secondRail := ?_
    }
    rw [List.disjoint_left]
    intro face hfirst hsecond
    have hsecondEq : face = cross.face := by simpa [hcrossStart] using hsecond
    have hrawCross : cross.face ∈ rawFirst.support :=
      hsecondEq ▸ rawFirst.support_bypass_subset_support hfirst
    simp only [rawFirst, SimpleGraph.Walk.support_append, List.mem_append]
      at hrawCross
    rcases hrawCross with (hold | hbridge) | hnew
    · exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
        hold) cross.mem_old
    · have hbridge' : cross.face =
            (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
              |>.faceAt leftInterior.center) ∨
          cross.face = selectedPlacementSideFace leftPlacement
            successor.frame.leftAfter := by
        simpa only [rightCenterBridge, selectedPlacementCenterBridge,
          SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false]
          using hbridge
      by_cases hcenter : cross.face =
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
            |>.faceAt leftInterior.center)
      · exact (left.paths.secondRail_support_adjacent_center cross.face
          cross.mem_old).ne hcenter.symm
      · have hafter : cross.face = selectedPlacementSideFace leftPlacement
            successor.frame.leftAfter := hbridge'.resolve_left hcenter
        have hcrossFirst : cross.face ∈ successor.firstContinuation.support :=
          List.mem_of_mem_tail cross.mem_new
        have hafterFull : selectedPlacementSideFace leftPlacement
            successor.frame.leftAfter ∈ successor.secondContinuation.support :=
          successor.secondContinuation.start_mem_support
        have hcrossSecond : cross.face ∈
            successor.secondContinuation.support := by
          simpa only [hafter] using hafterFull
        exact (List.disjoint_left.mp
          successor.firstContinuation_support_disjoint_secondContinuation
            hcrossFirst) hcrossSecond
    · exact (List.disjoint_left.mp
        successor.firstContinuation_support_disjoint_secondContinuation
          (List.mem_of_mem_tail cross.mem_new)) (List.mem_of_mem_tail hnew)
  · have hsameStart : same.face =
        selectedPlacementSideFace leftPlacement leftIncomingAfter :=
      (secondFirstSameSecond_cross_eq_start_or_same_eq_start
        cross same lengths).resolve_left hcrossStart
    refine Sum.inl ?_
    let firstRail := successor.firstContinuation.copy hfirstStart.symm rfl
    refine {
      firstRail := firstRail
      secondRail := SimpleGraph.Walk.nil.copy rfl
        (hsameStart.symm.trans hsameEnd)
      firstRail_isPath := by
        simpa [firstRail] using successor.firstContinuation_isPath
      secondRail_isPath := by simp
      firstRail_support_disjoint_secondRail := ?_
    }
    rw [List.disjoint_left]
    intro face hfirst hsecond
    have hsecondEq : face = same.face := by simpa [hsameStart] using hsecond
    have hfirst' : same.face ∈ successor.firstContinuation.support := by
      rw [SimpleGraph.Walk.support_copy] at hfirst
      simpa only [hsecondEq] using hfirst
    by_cases hstart : same.face = selectedPlacementSideFace leftPlacement
        successor.frame.leftBefore
    · exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
        (by simpa only [hstart] using left.paths.firstRail.end_mem_support))
        same.mem_old
    · have htail : same.face ∈ successor.firstContinuation.support.tail := by
        rw [← successor.firstContinuation.cons_tail_support] at hfirst'
        simpa only [List.mem_cons, hstart, false_or] using hfirst'
      have htailEnd := eq_end_of_mem_support_tail_of_length_le_one
        successor.firstContinuation (by omega) htail
      exact hcrossNeSame (hcrossEnd.trans htailEnd.symm)

/-- Rail exchange preserves finite adjacent-window provenance. -/
theorem appendSecondFirstSameSecond_supportContained
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.secondContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 0 ∧
      left.paths.secondRail.length = 2 ∧
      successor.firstContinuation.length = 1 ∧
      successor.secondContinuation.length = 1) :
    AssemblySumSupportedByAdjacentSelectedRailPieces (successor := successor)
      (left := left) (appendSecondFirstSameSecond cross same lengths) := by
  classical
  by_cases hcrossStart : cross.face =
      selectedPlacementSideFace leftPlacement leftIncomingAfter
  · simp only [appendSecondFirstSameSecond, hcrossStart,
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
      · exact mem_adjacentSelectedRailPieces_of_mem_rightCenterBridge_support
          (successor := successor) (left := left)
          (List.mem_of_mem_tail hbridge)
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (List.mem_of_mem_tail hnew))))
    · intro face hface
      have hfaceEq : face = cross.face := by simpa [hcrossStart] using hface
      exact Or.inr (Or.inr (Or.inl (hfaceEq ▸ cross.mem_old)))
  · simp only [appendSecondFirstSameSecond, hcrossStart,
      AssemblySumSupportedByAdjacentSelectedRailPieces,
      AssemblySupportedByAdjacentSelectedRailPieces]
    constructor
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      exact Or.inr (Or.inr (Or.inr (Or.inl hface)))
    · intro face hface
      have hsameStart : same.face =
          selectedPlacementSideFace leftPlacement leftIncomingAfter :=
        (secondFirstSameSecond_cross_eq_start_or_same_eq_start
          cross same lengths).resolve_left hcrossStart
      have hfaceEq : face = same.face := by simpa [hsameStart] using hface
      exact Or.inr (Or.inr (Or.inl (hfaceEq ▸ same.mem_old)))

/-- The symmetric stationary residue has the same track-sensitive
provenance, including the explicit three-face centre connector. -/
theorem appendSecondFirstSameSecond_trackProvenance
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.secondContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 0 ∧
      left.paths.secondRail.length = 2 ∧
      successor.firstContinuation.length = 1 ∧
      successor.secondContinuation.length = 1) :
    AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
      (left := left) (appendSecondFirstSameSecond cross same lengths) := by
  classical
  by_cases hcrossStart : cross.face =
      selectedPlacementSideFace leftPlacement leftIncomingAfter
  · simp only [appendSecondFirstSameSecond, hcrossStart,
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
      have hfaceEq : face = cross.face := by simpa [hcrossStart] using hface
      exact Or.inl (hfaceEq ▸ cross.mem_old)
  · simp only [appendSecondFirstSameSecond, hcrossStart,
      AssemblySumSupportedByExpectedSelectedRailTracks,
      FaceInExpectedSelectedRailTrack]
    constructor
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      exact Or.inr (Or.inl hface)
    · intro face hface
      have hsameStart : same.face =
          selectedPlacementSideFace leftPlacement leftIncomingAfter :=
        (secondFirstSameSecond_cross_eq_start_or_same_eq_start
          cross same lengths).resolve_left hcrossStart
      have hfaceEq : face = same.face := by simpa [hsameStart] using hface
      exact Or.inl (hfaceEq ▸ same.mem_old)

/-- Seam-reversed construction for the `firstSecondSameSecond` residue. -/
noncomputable def appendFirstSecondSameSecond
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.secondContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 1 ∧
      left.paths.secondRail.length = 1 ∧
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
  let crossActual :
      SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision
        successor left := ⟨cross.face, Or.inl ⟨cross.mem_old, cross.mem_new⟩⟩
  let sameActual :
      SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
        successor left := ⟨same.face, Or.inr (Or.inl
          ⟨same.mem_old, same.mem_new⟩)⟩
  have hcrossOldStart : cross.face =
      selectedPlacementSideFace leftPlacement leftIncomingBefore :=
    eq_start_of_mem_support_of_length_le_one_of_ne_end left.paths.firstRail
      (by omega) cross.mem_old crossActual.toAdjacentDualTriangle.third_ne_before
  have hsameOldStart : same.face =
      selectedPlacementSideFace leftPlacement leftIncomingAfter :=
    eq_start_of_mem_support_of_length_le_one_of_ne_end left.paths.secondRail
      (by omega) same.mem_old sameActual.toAdjacentDualTriangle.third_ne_after
  have hfirstFinish : selectedPlacementSideFace leftPlacement
      successor.frame.leftBefore = selectedPlacementSideFace rightPlacement
        successor.rightOutgoingBefore :=
    SimpleGraph.Walk.eq_of_length_eq_zero lengths.2.2.1
  have hcrossNeSame : cross.face ≠ same.face := by
    intro heq
    exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
      cross.mem_old) (heq ▸ same.mem_old)
  by_cases hcrossEnd : cross.face = selectedPlacementSideFace rightPlacement
      successor.rightOutgoingAfter
  · refine Sum.inr ?_
    let rawSecond :=
      (left.paths.secondRail.append (leftCenterBridge (successor := successor)
        (left := left))).append successor.firstContinuation
    refine {
      firstRail := SimpleGraph.Walk.nil.copy rfl
        (hcrossOldStart.symm.trans hcrossEnd)
      secondRail := rawSecond.bypass
      firstRail_isPath := by simp
      secondRail_isPath := rawSecond.bypass_isPath
      firstRail_support_disjoint_secondRail := ?_
    }
    rw [List.disjoint_left]
    intro face hfirst hsecond
    have hfirstEq : face = cross.face := by
      simpa [hcrossOldStart] using hfirst
    have hrawCross : cross.face ∈ rawSecond.support :=
      hfirstEq ▸ rawSecond.support_bypass_subset_support hsecond
    simp only [rawSecond, SimpleGraph.Walk.support_append, List.mem_append]
      at hrawCross
    rcases hrawCross with (hold | hbridge) | hnew
    · exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
        cross.mem_old) hold
    · have hbridge' : cross.face =
            (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
              |>.faceAt leftInterior.center) ∨
          cross.face = selectedPlacementSideFace leftPlacement
            successor.frame.leftBefore := by
        simpa only [leftCenterBridge, selectedPlacementCenterBridge,
          SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false]
          using hbridge
      rcases hbridge' with hcenter | hbefore
      · exact (left.paths.firstRail_support_adjacent_center cross.face
          cross.mem_old).ne hcenter.symm
      · exact crossActual.toAdjacentDualTriangle.third_ne_before hbefore
    · have htailEmpty : successor.firstContinuation.support.tail = [] :=
        support_tail_eq_nil_of_length_eq_zero successor.firstContinuation
          lengths.2.2.1
      rw [htailEmpty] at hnew
      exact List.not_mem_nil hnew
  · have hsameEnd : same.face = selectedPlacementSideFace rightPlacement
        successor.rightOutgoingAfter :=
      (firstSecondSameSecond_cross_eq_end_or_same_eq_end
        cross same lengths).resolve_left hcrossEnd
    refine Sum.inl ?_
    let firstRail := left.paths.firstRail.copy rfl hfirstFinish
    refine {
      firstRail := firstRail
      secondRail := SimpleGraph.Walk.nil.copy rfl
        (hsameOldStart.symm.trans hsameEnd)
      firstRail_isPath := by simpa [firstRail] using left.paths.firstRail_isPath
      secondRail_isPath := by simp
      firstRail_support_disjoint_secondRail := ?_
    }
    rw [List.disjoint_left]
    intro face hfirst hsecond
    have hsecondEq : face = same.face := by simpa [hsameOldStart] using hsecond
    rw [SimpleGraph.Walk.support_copy] at hfirst
    exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
      hfirst) (by simpa only [hsecondEq] using same.mem_old)

/-- Seam reversal preserves finite adjacent-window provenance. -/
theorem appendFirstSecondSameSecond_supportContained
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.secondContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 1 ∧
      left.paths.secondRail.length = 1 ∧
      successor.firstContinuation.length = 0 ∧
      successor.secondContinuation.length = 2) :
    AssemblySumSupportedByAdjacentSelectedRailPieces (successor := successor)
      (left := left) (appendFirstSecondSameSecond cross same lengths) := by
  classical
  by_cases hcrossEnd : cross.face =
      selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter
  · simp only [appendFirstSecondSameSecond, hcrossEnd,
      AssemblySumSupportedByAdjacentSelectedRailPieces,
      AssemblySupportedByAdjacentSelectedRailPieces]
    constructor
    · intro face hface
      let actual :
          SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision
            successor left := ⟨cross.face, Or.inl ⟨cross.mem_old, cross.mem_new⟩⟩
      have hcrossOldStart : cross.face =
          selectedPlacementSideFace leftPlacement leftIncomingBefore :=
        eq_start_of_mem_support_of_length_le_one_of_ne_end left.paths.firstRail
          (by omega) cross.mem_old actual.toAdjacentDualTriangle.third_ne_before
      have hfaceEq : face = cross.face := by simpa [hcrossOldStart] using hface
      exact Or.inr (Or.inl (hfaceEq ▸ cross.mem_old))
    · intro face hface
      let rawSecond :=
        (left.paths.secondRail.append (leftCenterBridge (successor := successor)
          (left := left))).append successor.firstContinuation
      have hraw : face ∈ rawSecond.support :=
        rawSecond.support_bypass_subset_support hface
      simp only [rawSecond, SimpleGraph.Walk.support_append, List.mem_append] at hraw
      rcases hraw with (hold | hbridge) | hnew
      · exact Or.inr (Or.inr (Or.inl hold))
      · exact mem_adjacentSelectedRailPieces_of_mem_leftCenterBridge_support
          (successor := successor) (left := left)
          (List.mem_of_mem_tail hbridge)
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          (List.mem_of_mem_tail hnew))))
  · simp only [appendFirstSecondSameSecond, hcrossEnd,
      AssemblySumSupportedByAdjacentSelectedRailPieces,
      AssemblySupportedByAdjacentSelectedRailPieces]
    constructor
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      exact Or.inr (Or.inl hface)
    · intro face hface
      let actual :
          SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
            successor left :=
        ⟨same.face, Or.inr (Or.inl ⟨same.mem_old, same.mem_new⟩)⟩
      have hsameEnd : same.face = selectedPlacementSideFace rightPlacement
          successor.rightOutgoingAfter :=
        (firstSecondSameSecond_cross_eq_end_or_same_eq_end
          cross same lengths).resolve_left hcrossEnd
      have hsameOldStart : same.face =
          selectedPlacementSideFace leftPlacement leftIncomingAfter :=
        eq_start_of_mem_support_of_length_le_one_of_ne_end left.paths.secondRail
          (by omega) same.mem_old actual.toAdjacentDualTriangle.third_ne_after
      have hfaceEq : face = same.face := by simpa [hsameOldStart, hsameEnd] using hface
      exact Or.inr (Or.inr (Or.inl (hfaceEq ▸ same.mem_old)))

/-- Seam reversal does not erase rail identity: each output uses its named
old rail, its endpoint-selected successor rail, and only the literal centre
connector faces. -/
theorem appendFirstSecondSameSecond_trackProvenance
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.secondContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 1 ∧
      left.paths.secondRail.length = 1 ∧
      successor.firstContinuation.length = 0 ∧
      successor.secondContinuation.length = 2) :
    AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
      (left := left) (appendFirstSecondSameSecond cross same lengths) := by
  classical
  by_cases hcrossEnd : cross.face =
      selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter
  · simp only [appendFirstSecondSameSecond, hcrossEnd,
      AssemblySumSupportedByExpectedSelectedRailTracks,
      FaceInExpectedSelectedRailTrack]
    constructor
    · intro face hface
      let actual :
          SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision
            successor left := ⟨cross.face, Or.inl ⟨cross.mem_old, cross.mem_new⟩⟩
      have hcrossOldStart : cross.face =
          selectedPlacementSideFace leftPlacement leftIncomingBefore :=
        eq_start_of_mem_support_of_length_le_one_of_ne_end left.paths.firstRail
          (by omega) cross.mem_old actual.toAdjacentDualTriangle.third_ne_before
      have hfaceEq : face = cross.face := by simpa [hcrossOldStart] using hface
      exact Or.inl (hfaceEq ▸ cross.mem_old)
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
  · simp only [appendFirstSecondSameSecond, hcrossEnd,
      AssemblySumSupportedByExpectedSelectedRailTracks,
      FaceInExpectedSelectedRailTrack]
    constructor
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      exact Or.inl hface
    · intro face hface
      let actual :
          SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
            successor left :=
        ⟨same.face, Or.inr (Or.inl ⟨same.mem_old, same.mem_new⟩)⟩
      have hsameEnd : same.face = selectedPlacementSideFace rightPlacement
          successor.rightOutgoingAfter :=
        (firstSecondSameSecond_cross_eq_end_or_same_eq_end
          cross same lengths).resolve_left hcrossEnd
      have hsameOldStart : same.face =
          selectedPlacementSideFace leftPlacement leftIncomingAfter :=
        eq_start_of_mem_support_of_length_le_one_of_ne_end left.paths.secondRail
          (by omega) same.mem_old actual.toAdjacentDualTriangle.third_ne_after
      have hfaceEq : face = same.face := by
        simpa [hsameOldStart, hsameEnd] using hface
      exact Or.inl (hfaceEq ▸ same.mem_old)

/-- Rail-exchanged seam-reversed construction for
`secondFirstSameFirst`. -/
noncomputable def appendSecondFirstSameFirst
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.firstContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 1 ∧
      left.paths.secondRail.length = 1 ∧
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
  let crossActual :
      SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision
        successor left := ⟨cross.face, Or.inr ⟨cross.mem_old, cross.mem_new⟩⟩
  let sameActual :
      SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
        successor left := ⟨same.face, Or.inl ⟨same.mem_old, same.mem_new⟩⟩
  have hcrossOldStart : cross.face =
      selectedPlacementSideFace leftPlacement leftIncomingAfter :=
    eq_start_of_mem_support_of_length_le_one_of_ne_end left.paths.secondRail
      (by omega) cross.mem_old crossActual.toAdjacentDualTriangle.third_ne_after
  have hsameOldStart : same.face =
      selectedPlacementSideFace leftPlacement leftIncomingBefore :=
    eq_start_of_mem_support_of_length_le_one_of_ne_end left.paths.firstRail
      (by omega) same.mem_old sameActual.toAdjacentDualTriangle.third_ne_before
  have hsecondFinish : selectedPlacementSideFace leftPlacement
      successor.frame.leftAfter = selectedPlacementSideFace rightPlacement
        successor.rightOutgoingAfter :=
    SimpleGraph.Walk.eq_of_length_eq_zero lengths.2.2.2
  have hcrossNeSame : cross.face ≠ same.face := by
    intro heq
    exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
      (heq ▸ same.mem_old)) cross.mem_old
  by_cases hcrossEnd : cross.face = selectedPlacementSideFace rightPlacement
      successor.rightOutgoingBefore
  · refine Sum.inr ?_
    let rawFirst :=
      (left.paths.firstRail.append (rightCenterBridge (successor := successor)
        (left := left))).append successor.secondContinuation
    refine {
      firstRail := rawFirst.bypass
      secondRail := SimpleGraph.Walk.nil.copy rfl
        (hcrossOldStart.symm.trans hcrossEnd)
      firstRail_isPath := rawFirst.bypass_isPath
      secondRail_isPath := by simp
      firstRail_support_disjoint_secondRail := ?_
    }
    rw [List.disjoint_left]
    intro face hfirst hsecond
    have hsecondEq : face = cross.face := by
      simpa [hcrossOldStart] using hsecond
    have hrawCross : cross.face ∈ rawFirst.support :=
      hsecondEq ▸ rawFirst.support_bypass_subset_support hfirst
    simp only [rawFirst, SimpleGraph.Walk.support_append, List.mem_append]
      at hrawCross
    rcases hrawCross with (hold | hbridge) | hnew
    · exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
        hold) cross.mem_old
    · have hbridge' : cross.face =
            (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
              |>.faceAt leftInterior.center) ∨
          cross.face = selectedPlacementSideFace leftPlacement
            successor.frame.leftAfter := by
        simpa only [rightCenterBridge, selectedPlacementCenterBridge,
          SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false]
          using hbridge
      rcases hbridge' with hcenter | hafter
      · exact (left.paths.secondRail_support_adjacent_center cross.face
          cross.mem_old).ne hcenter.symm
      · exact crossActual.toAdjacentDualTriangle.third_ne_after hafter
    · have htailEmpty : successor.secondContinuation.support.tail = [] :=
        support_tail_eq_nil_of_length_eq_zero successor.secondContinuation
          lengths.2.2.2
      rw [htailEmpty] at hnew
      exact List.not_mem_nil hnew
  · have hsameEnd : same.face = selectedPlacementSideFace rightPlacement
        successor.rightOutgoingBefore :=
      (secondFirstSameFirst_cross_eq_end_or_same_eq_end
        cross same lengths).resolve_left hcrossEnd
    refine Sum.inl ?_
    let secondRail := left.paths.secondRail.copy rfl hsecondFinish
    refine {
      firstRail := SimpleGraph.Walk.nil.copy rfl
        (hsameOldStart.symm.trans hsameEnd)
      secondRail := secondRail
      firstRail_isPath := by simp
      secondRail_isPath := by
        simpa [secondRail] using left.paths.secondRail_isPath
      firstRail_support_disjoint_secondRail := ?_
    }
    rw [List.disjoint_left]
    intro face hfirst hsecond
    have hfirstEq : face = same.face := by simpa [hsameOldStart] using hfirst
    rw [SimpleGraph.Walk.support_copy] at hsecond
    exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
      (by simpa only [hfirstEq] using same.mem_old)) hsecond

/-- Rail exchange and seam reversal together preserve finite provenance. -/
theorem appendSecondFirstSameFirst_supportContained
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.firstContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 1 ∧
      left.paths.secondRail.length = 1 ∧
      successor.firstContinuation.length = 2 ∧
      successor.secondContinuation.length = 0) :
    AssemblySumSupportedByAdjacentSelectedRailPieces (successor := successor)
      (left := left) (appendSecondFirstSameFirst cross same lengths) := by
  classical
  by_cases hcrossEnd : cross.face =
      selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore
  · simp only [appendSecondFirstSameFirst, hcrossEnd,
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
      · exact mem_adjacentSelectedRailPieces_of_mem_rightCenterBridge_support
          (successor := successor) (left := left)
          (List.mem_of_mem_tail hbridge)
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (List.mem_of_mem_tail hnew))))
    · intro face hface
      let actual :
          SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision
            successor left := ⟨cross.face, Or.inr ⟨cross.mem_old, cross.mem_new⟩⟩
      have hcrossOldStart : cross.face =
          selectedPlacementSideFace leftPlacement leftIncomingAfter :=
        eq_start_of_mem_support_of_length_le_one_of_ne_end left.paths.secondRail
          (by omega) cross.mem_old actual.toAdjacentDualTriangle.third_ne_after
      have hfaceEq : face = cross.face := by simpa [hcrossOldStart] using hface
      exact Or.inr (Or.inr (Or.inl (hfaceEq ▸ cross.mem_old)))
  · simp only [appendSecondFirstSameFirst, hcrossEnd,
      AssemblySumSupportedByAdjacentSelectedRailPieces,
      AssemblySupportedByAdjacentSelectedRailPieces]
    constructor
    · intro face hface
      let actual :
          SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
            successor left := ⟨same.face, Or.inl ⟨same.mem_old, same.mem_new⟩⟩
      have hsameEnd : same.face = selectedPlacementSideFace rightPlacement
          successor.rightOutgoingBefore :=
        (secondFirstSameFirst_cross_eq_end_or_same_eq_end
          cross same lengths).resolve_left hcrossEnd
      have hsameOldStart : same.face =
          selectedPlacementSideFace leftPlacement leftIncomingBefore :=
        eq_start_of_mem_support_of_length_le_one_of_ne_end left.paths.firstRail
          (by omega) same.mem_old actual.toAdjacentDualTriangle.third_ne_before
      have hfaceEq : face = same.face := by simpa [hsameOldStart, hsameEnd] using hface
      exact Or.inr (Or.inl (hfaceEq ▸ same.mem_old))
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      exact Or.inr (Or.inr (Or.inl hface))

/-- The rail-exchanged seam-reversed residue also preserves the two expected
tracks modulo the explicit three-face centre connector. -/
theorem appendSecondFirstSameFirst_trackProvenance
    (cross : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail)
    (same : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.firstContinuation.support.tail)
    (lengths : left.paths.firstRail.length = 1 ∧
      left.paths.secondRail.length = 1 ∧
      successor.firstContinuation.length = 2 ∧
      successor.secondContinuation.length = 0) :
    AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
      (left := left) (appendSecondFirstSameFirst cross same lengths) := by
  classical
  by_cases hcrossEnd : cross.face =
      selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore
  · simp only [appendSecondFirstSameFirst, hcrossEnd,
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
      let actual :
          SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision
            successor left := ⟨cross.face, Or.inr ⟨cross.mem_old, cross.mem_new⟩⟩
      have hcrossOldStart : cross.face =
          selectedPlacementSideFace leftPlacement leftIncomingAfter :=
        eq_start_of_mem_support_of_length_le_one_of_ne_end left.paths.secondRail
          (by omega) cross.mem_old actual.toAdjacentDualTriangle.third_ne_after
      have hfaceEq : face = cross.face := by simpa [hcrossOldStart] using hface
      exact Or.inl (hfaceEq ▸ cross.mem_old)
  · simp only [appendSecondFirstSameFirst, hcrossEnd,
      AssemblySumSupportedByExpectedSelectedRailTracks,
      FaceInExpectedSelectedRailTrack]
    constructor
    · intro face hface
      let actual :
          SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
            successor left := ⟨same.face, Or.inl ⟨same.mem_old, same.mem_new⟩⟩
      have hsameEnd : same.face = selectedPlacementSideFace rightPlacement
          successor.rightOutgoingBefore :=
        (secondFirstSameFirst_cross_eq_end_or_same_eq_end
          cross same lengths).resolve_left hcrossEnd
      have hsameOldStart : same.face =
          selectedPlacementSideFace leftPlacement leftIncomingBefore :=
        eq_start_of_mem_support_of_length_le_one_of_ne_end left.paths.firstRail
          (by omega) same.mem_old actual.toAdjacentDualTriangle.third_ne_before
      have hfaceEq : face = same.face := by
        simpa [hsameOldStart, hsameEnd] using hface
      exact Or.inl (hfaceEq ▸ same.mem_old)
    · intro face hface
      rw [SimpleGraph.Walk.support_copy] at hface
      exact Or.inl hface

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
