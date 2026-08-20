import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailConstructionTrace

/-!
# L1: track provenance for the canonical adjacent rail construction

The exact terminal-window certificate retains a five-piece support envelope,
but that envelope forgets which old rail and which successor rail contribute
to each output.  The finite construction trace is stronger: every principal,
immediate centre-bridge, stationary-residue, and centre-revisit constructor
selects a definite pair of tracks.

This module proves that invariant for the complete canonical append.  A
straight output uses old-first/new-first and old-second/new-second; an
endpoint-exchanged output crosses only the successor tracks.  In either case
the only additional faces are the two named seam flanks and the displayed
Cell-3 centre used by a literal connector.

This is proof-relevant collision input.  It does not yet eliminate a retained
four-cell collision, construct the rolling arbitrary-length transition,
attach either end cap, or close Fable flag L1.
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

/-- Track-sensitive provenance on the public straight-or-swapped result. -/
def SelectedLocalRailAppendCompleteOutcome.HasTrackProvenance
    (result : SelectedLocalRailAppendCompleteOutcome successor left) : Prop :=
  match result with
  | .straight assembly =>
      AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
        (left := left) (.inl assembly)
  | .swapped assembly =>
      AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
        (left := left) (.inr assembly)

/-- The principal disjoint append stays on the two straight tracks. -/
theorem appendSuccessorBypass_trackProvenance
    (hfirstSecond : left.paths.firstRail.support.Disjoint
      successor.secondContinuation.support.tail)
    (hsecondFirst : left.paths.secondRail.support.Disjoint
      successor.firstContinuation.support.tail) :
    AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
      (left := left) (.inl
        (appendSuccessorBypass successor left.toAssembly
          hfirstSecond hsecondFirst)) := by
  simp only [AssemblySumSupportedByExpectedSelectedRailTracks,
    FaceInExpectedSelectedRailTrack]
  constructor
  · intro face hface
    have hraw :=
      (left.paths.firstRail.append successor.firstContinuation
        |>.support_bypass_subset_support) hface
    rw [SimpleGraph.Walk.support_append] at hraw
    rcases List.mem_append.mp hraw with hold | hnew
    · exact Or.inl hold
    · exact Or.inr (Or.inl (List.mem_of_mem_tail hnew))
  · intro face hface
    have hraw :=
      (left.paths.secondRail.append successor.secondContinuation
        |>.support_bypass_subset_support) hface
    rw [SimpleGraph.Walk.support_append] at hraw
    rcases List.mem_append.mp hraw with hold | hnew
    · exact Or.inl hold
    · exact Or.inr (Or.inl (List.mem_of_mem_tail hnew))

/-- The principal crossed repair exchanges exactly the successor tracks. -/
theorem appendSuccessorSwapBothCrossCollisions_trackProvenance
    (firstSecondFace secondFirstFace :
      AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hfirstSecondOld : firstSecondFace ∈ left.paths.firstRail.support)
    (hfirstSecondNew :
      firstSecondFace ∈ successor.secondContinuation.support.tail)
    (hsecondFirstOld : secondFirstFace ∈ left.paths.secondRail.support)
    (hsecondFirstNew :
      secondFirstFace ∈ successor.firstContinuation.support.tail)
    (hfirstFirst : left.paths.firstRail.support.Disjoint
      successor.firstContinuation.support.tail)
    (hsecondSecond : left.paths.secondRail.support.Disjoint
      successor.secondContinuation.support.tail) :
    AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
      (left := left) (.inr
        (appendSuccessorSwapBothCrossCollisions successor left
          firstSecondFace secondFirstFace hfirstSecondOld hfirstSecondNew
          hsecondFirstOld hsecondFirstNew hfirstFirst hsecondSecond)) := by
  simp only [AssemblySumSupportedByExpectedSelectedRailTracks,
    FaceInExpectedSelectedRailTrack]
  constructor
  · intro face hface
    let reroute :=
      SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
        (successor := successor) (left := left) firstSecondFace
          hfirstSecondOld hfirstSecondNew
    rcases reroute.route_support_subset face hface with hold | hnew
    · exact Or.inl hold
    · exact Or.inr (Or.inl (List.mem_of_mem_tail hnew))
  · intro face hface
    let reroute :=
      SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
        (successor := successor) (left := left) secondFirstFace
          hsecondFirstOld hsecondFirstNew
    rcases reroute.route_support_subset face hface with hold | hnew
    · exact Or.inl hold
    · exact Or.inr (Or.inl (List.mem_of_mem_tail hnew))

/-- Track predicate on the first exhaustive classifier. -/
def SelectedLocalRailAppendOutcome.HasTrackProvenance
    (result : SelectedLocalRailAppendOutcome successor left) : Prop :=
  match result with
  | .straight assembly =>
      AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
        (left := left) (.inl assembly)
  | .swapped assembly =>
      AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
        (left := left) (.inr assembly)
  | .singleFirstSecond _ _ | .singleSecondFirst _ _ |
      .doubleCrossSameTrack _ _ _ => True

theorem classifyLocalSuccessorAppend_hasTrackProvenance :
    (classifyLocalSuccessorAppend successor left).HasTrackProvenance := by
  classical
  unfold classifyLocalSuccessorAppend
  split
  · rename_i hfirstSecond
    split
    · rename_i hsecondFirst
      exact appendSuccessorBypass_trackProvenance hfirstSecond hsecondFirst
    · trivial
  · rename_i hfirstSecond
    dsimp only
    split
    · trivial
    · rename_i hsecondFirst
      split
      · rename_i hfirstFirst
        split
        · rename_i hsecondSecond
          exact appendSuccessorSwapBothCrossCollisions_trackProvenance
            (SelectedRailSupportCollision.of_not_disjoint hfirstSecond).face
            (SelectedRailSupportCollision.of_not_disjoint hsecondFirst).face
            (SelectedRailSupportCollision.of_not_disjoint hfirstSecond).mem_old
            (SelectedRailSupportCollision.of_not_disjoint hfirstSecond).mem_new
            (SelectedRailSupportCollision.of_not_disjoint hsecondFirst).mem_old
            (SelectedRailSupportCollision.of_not_disjoint hsecondFirst).mem_new
            hfirstFirst hsecondSecond
        · trivial
      · trivial

/-- Track predicate after the impossible mixed double-cross branch is
removed. -/
def SelectedLocalRailAppendResolvedOutcome.HasTrackProvenance
    (result : SelectedLocalRailAppendResolvedOutcome successor left) : Prop :=
  match result with
  | .straight assembly =>
      AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
        (left := left) (.inl assembly)
  | .swapped assembly =>
      AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
        (left := left) (.inr assembly)
  | .singleFirstSecond _ _ | .singleSecondFirst _ _ => True

theorem classifyLocalSuccessorAppendResolved_hasTrackProvenance :
    (classifyLocalSuccessorAppendResolved successor left).HasTrackProvenance := by
  classical
  have hbase := classifyLocalSuccessorAppend_hasTrackProvenance
    (successor := successor) (left := left)
  cases hresult : classifyLocalSuccessorAppend successor left with
  | straight assembly =>
      simpa [classifyLocalSuccessorAppendResolved, hresult,
        SelectedLocalRailAppendOutcome.HasTrackProvenance,
        SelectedLocalRailAppendResolvedOutcome.HasTrackProvenance] using hbase
  | swapped assembly =>
      simpa [classifyLocalSuccessorAppendResolved, hresult,
        SelectedLocalRailAppendOutcome.HasTrackProvenance,
        SelectedLocalRailAppendResolvedOutcome.HasTrackProvenance] using hbase
  | singleFirstSecond _ _ =>
      simp [classifyLocalSuccessorAppendResolved, hresult,
        SelectedLocalRailAppendResolvedOutcome.HasTrackProvenance]
  | singleSecondFirst _ _ =>
      simp [classifyLocalSuccessorAppendResolved, hresult,
        SelectedLocalRailAppendResolvedOutcome.HasTrackProvenance]
  | doubleCrossSameTrack firstSecond secondFirst sameTrack =>
      exact False.elim (not_doubleCrossSameTrack firstSecond secondFirst sameTrack)

/-- Track predicate for the first immediate centre-bridge classifier. -/
def SingleFirstSecondCenterBridgeOutcome.HasTrackProvenance
    {collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail}
    (result : SingleFirstSecondCenterBridgeOutcome collision) : Prop :=
  match result with
  | .assembly value =>
      AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
        (left := left) (.inr value)
  | .meetsOldSecond _ | .meetsNewFirst _ | .containsLeftCenter _ => True

theorem classifySingleFirstSecondCenterBridge_hasTrackProvenance
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail) :
    (classifySingleFirstSecondCenterBridge collision).HasTrackProvenance := by
  classical
  unfold classifySingleFirstSecondCenterBridge
  dsimp only
  split
  · rename_i holdSecond
    split
    · rename_i hnewFirst
      split
      · trivial
      · rename_i hcenter
        simpa [SingleFirstSecondCenterBridgeOutcome.HasTrackProvenance,
          AssemblySumSupportedByExpectedSelectedRailTracks,
          FaceInExpectedSelectedRailTrack] using
          appendSingleFirstSecondViaLeftCenter_trackProvenance
            collision holdSecond hnewFirst hcenter
    · trivial
  · trivial

/-- Symmetric immediate centre-bridge track predicate. -/
def SingleSecondFirstCenterBridgeOutcome.HasTrackProvenance
    {collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail}
    (result : SingleSecondFirstCenterBridgeOutcome collision) : Prop :=
  match result with
  | .assembly value =>
      AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
        (left := left) (.inr value)
  | .meetsOldFirst _ | .meetsNewSecond _ | .containsLeftCenter _ => True

theorem classifySingleSecondFirstCenterBridge_hasTrackProvenance
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail) :
    (classifySingleSecondFirstCenterBridge collision).HasTrackProvenance := by
  classical
  unfold classifySingleSecondFirstCenterBridge
  dsimp only
  split
  · rename_i holdFirst
    split
    · rename_i hnewSecond
      split
      · trivial
      · rename_i hcenter
        simpa [SingleSecondFirstCenterBridgeOutcome.HasTrackProvenance,
          AssemblySumSupportedByExpectedSelectedRailTracks,
          FaceInExpectedSelectedRailTrack] using
          appendSingleSecondFirstViaLeftCenter_trackProvenance
            collision holdFirst hnewSecond hcenter
    · trivial
  · trivial

/-- Track predicate on the final finite length classifier. -/
def SelectedLocalRailAppendLengthResolvedOutcome.HasTrackProvenance
    (result : SelectedLocalRailAppendLengthResolvedOutcome successor left) : Prop :=
  match result with
  | .straight assembly =>
      AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
        (left := left) (.inl assembly)
  | .swapped assembly =>
      AssemblySumSupportedByExpectedSelectedRailTracks (successor := successor)
        (left := left) (.inr assembly)
  | .firstSecondSameFirst _ _ _ | .firstSecondSameSecond _ _ _ |
      .firstSecondCenter _ _ _ | .secondFirstSameFirst _ _ _ |
      .secondFirstSameSecond _ _ _ | .secondFirstCenter _ _ _ => True

theorem classifyLocalSuccessorAppendLengthResolved_hasTrackProvenance :
    (classifyLocalSuccessorAppendLengthResolved successor left)
      |>.HasTrackProvenance := by
  classical
  have hresolved := classifyLocalSuccessorAppendResolved_hasTrackProvenance
    (successor := successor) (left := left)
  cases hresult : classifyLocalSuccessorAppendResolved successor left with
  | straight assembly =>
      simpa [classifyLocalSuccessorAppendLengthResolved, hresult,
        SelectedLocalRailAppendResolvedOutcome.HasTrackProvenance,
        SelectedLocalRailAppendLengthResolvedOutcome.HasTrackProvenance]
        using hresolved
  | swapped assembly =>
      simpa [classifyLocalSuccessorAppendLengthResolved, hresult,
        SelectedLocalRailAppendResolvedOutcome.HasTrackProvenance,
        SelectedLocalRailAppendLengthResolvedOutcome.HasTrackProvenance]
        using hresolved
  | singleFirstSecond cross _ =>
      have hs := classifySingleFirstSecondCenterBridge_hasTrackProvenance cross
      cases hcenter : classifySingleFirstSecondCenterBridge cross with
      | assembly value =>
          simpa [classifyLocalSuccessorAppendLengthResolved, hresult, hcenter,
            SingleFirstSecondCenterBridgeOutcome.HasTrackProvenance,
            SelectedLocalRailAppendLengthResolvedOutcome.HasTrackProvenance]
            using hs
      | meetsOldSecond _ => simp [classifyLocalSuccessorAppendLengthResolved,
          hresult, hcenter,
          SelectedLocalRailAppendLengthResolvedOutcome.HasTrackProvenance]
      | meetsNewFirst _ => simp [classifyLocalSuccessorAppendLengthResolved,
          hresult, hcenter,
          SelectedLocalRailAppendLengthResolvedOutcome.HasTrackProvenance]
      | containsLeftCenter _ => simp [classifyLocalSuccessorAppendLengthResolved,
          hresult, hcenter,
          SelectedLocalRailAppendLengthResolvedOutcome.HasTrackProvenance]
  | singleSecondFirst cross _ =>
      have hs := classifySingleSecondFirstCenterBridge_hasTrackProvenance cross
      cases hcenter : classifySingleSecondFirstCenterBridge cross with
      | assembly value =>
          simpa [classifyLocalSuccessorAppendLengthResolved, hresult, hcenter,
            SingleSecondFirstCenterBridgeOutcome.HasTrackProvenance,
            SelectedLocalRailAppendLengthResolvedOutcome.HasTrackProvenance]
            using hs
      | meetsOldFirst _ => simp [classifyLocalSuccessorAppendLengthResolved,
          hresult, hcenter,
          SelectedLocalRailAppendLengthResolvedOutcome.HasTrackProvenance]
      | meetsNewSecond _ => simp [classifyLocalSuccessorAppendLengthResolved,
          hresult, hcenter,
          SelectedLocalRailAppendLengthResolvedOutcome.HasTrackProvenance]
      | containsLeftCenter _ => simp [classifyLocalSuccessorAppendLengthResolved,
          hresult, hcenter,
          SelectedLocalRailAppendLengthResolvedOutcome.HasTrackProvenance]

/-- **L1 canonical track provenance.** Every branch of the actual complete
adjacent append stays on its endpoint-selected rail tracks, modulo only the
three explicitly named connector faces. -/
theorem appendLocalSuccessorComplete_hasTrackProvenance :
    (appendLocalSuccessorComplete successor left).HasTrackProvenance := by
  classical
  have hlength :=
    classifyLocalSuccessorAppendLengthResolved_hasTrackProvenance
      (successor := successor) (left := left)
  cases hresult : classifyLocalSuccessorAppendLengthResolved successor left with
  | straight assembly =>
      simpa [appendLocalSuccessorComplete, hresult,
        SelectedLocalRailAppendLengthResolvedOutcome.HasTrackProvenance,
        SelectedLocalRailAppendCompleteOutcome.HasTrackProvenance] using hlength
  | swapped assembly =>
      simpa [appendLocalSuccessorComplete, hresult,
        SelectedLocalRailAppendLengthResolvedOutcome.HasTrackProvenance,
        SelectedLocalRailAppendCompleteOutcome.HasTrackProvenance] using hlength
  | firstSecondSameFirst cross same lengths =>
      have hs := appendFirstSecondSameFirst_trackProvenance cross same lengths
      cases hrepair : appendFirstSecondSameFirst cross same lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumSupportedByExpectedSelectedRailTracks,
          SelectedLocalRailAppendCompleteOutcome.HasTrackProvenance] using hs
  | firstSecondSameSecond cross same lengths =>
      have hs := appendFirstSecondSameSecond_trackProvenance cross same lengths
      cases hrepair : appendFirstSecondSameSecond cross same lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumSupportedByExpectedSelectedRailTracks,
          SelectedLocalRailAppendCompleteOutcome.HasTrackProvenance] using hs
  | firstSecondCenter cross center lengths =>
      have hs := appendFirstSecondCenter_trackProvenance cross center lengths
      cases hrepair : appendFirstSecondCenter cross center lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumSupportedByExpectedSelectedRailTracks,
          SelectedLocalRailAppendCompleteOutcome.HasTrackProvenance] using hs
  | secondFirstSameFirst cross same lengths =>
      have hs := appendSecondFirstSameFirst_trackProvenance cross same lengths
      cases hrepair : appendSecondFirstSameFirst cross same lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumSupportedByExpectedSelectedRailTracks,
          SelectedLocalRailAppendCompleteOutcome.HasTrackProvenance] using hs
  | secondFirstSameSecond cross same lengths =>
      have hs := appendSecondFirstSameSecond_trackProvenance cross same lengths
      cases hrepair : appendSecondFirstSameSecond cross same lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumSupportedByExpectedSelectedRailTracks,
          SelectedLocalRailAppendCompleteOutcome.HasTrackProvenance] using hs
  | secondFirstCenter cross center lengths =>
      have hs := appendSecondFirstCenter_trackProvenance cross center lengths
      cases hrepair : appendSecondFirstCenter cross center lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumSupportedByExpectedSelectedRailTracks,
          SelectedLocalRailAppendCompleteOutcome.HasTrackProvenance] using hs

/-- A proof-relevant construction trace exposes the canonical track
provenance of its public outcome. -/
def ExactSelectedLocalRailConstructionTrace.HasTrackProvenance
    (trace : ExactSelectedLocalRailConstructionTrace successor left) : Prop :=
  trace.toOutcome.HasTrackProvenance

theorem ExactSelectedLocalRailConstructionTrace.hasTrackProvenance
    (trace : ExactSelectedLocalRailConstructionTrace successor left) :
    trace.HasTrackProvenance := by
  rw [ExactSelectedLocalRailConstructionTrace.HasTrackProvenance,
    trace.toOutcome_eq_complete]
  exact appendLocalSuccessorComplete_hasTrackProvenance

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
