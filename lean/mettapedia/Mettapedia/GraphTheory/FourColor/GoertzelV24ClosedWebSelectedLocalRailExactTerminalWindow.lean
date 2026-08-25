import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailTerminalWindow

/-!
# L1: exact finite-piece provenance for the terminal rail window

Remote separation needs only a closed two-centre neighbourhood, but the next
local repair needs to know which literal Cell-3 pieces may contain a support
face.  Every branch of the complete adjacent classifier already proves this
stronger fact.  This module retains it instead of discarding it at the
terminal-window boundary.

The exact package projects to the earlier coarse package, so existing remote
separation consumers remain unchanged.  This does not itself repair a
four-cell collision, iterate the window, attach an end cap, or close L1.
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

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- Exact finite-piece provenance on a complete straight-or-swapped result. -/
def SelectedLocalRailAppendCompleteOutcome.HasExactWindowProvenance
    (result : SelectedLocalRailAppendCompleteOutcome successor left) : Prop :=
  match result with
  | .straight assembly =>
      AssemblySupportedByAdjacentSelectedRailPieces (successor := successor)
        (left := left) assembly
  | .swapped assembly =>
      AssemblySupportedByAdjacentSelectedRailPieces (successor := successor)
        (left := left) assembly

/-- Exact support containment for the principal loop-erased append. -/
theorem appendSuccessorBypass_supportedByAdjacentSelectedRailPieces
    (hfirstSecond : left.paths.firstRail.support.Disjoint
      successor.secondContinuation.support.tail)
    (hsecondFirst : left.paths.secondRail.support.Disjoint
      successor.firstContinuation.support.tail) :
    AssemblySupportedByAdjacentSelectedRailPieces (successor := successor)
      (left := left)
      (appendSuccessorBypass successor left.toAssembly
        hfirstSecond hsecondFirst) := by
  constructor
  · intro face hface
    have hraw :=
      (left.paths.firstRail.append successor.firstContinuation
        |>.support_bypass_subset_support) hface
    rw [SimpleGraph.Walk.support_append] at hraw
    rcases List.mem_append.mp hraw with hold | hnew
    · exact Or.inr (Or.inl hold)
    · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_tail hnew))))
  · intro face hface
    have hraw :=
      (left.paths.secondRail.append successor.secondContinuation
        |>.support_bypass_subset_support) hface
    rw [SimpleGraph.Walk.support_append] at hraw
    rcases List.mem_append.mp hraw with hold | hnew
    · exact Or.inr (Or.inr (Or.inl hold))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (List.mem_of_mem_tail hnew))))

/-- Exact support containment for the principal crossed reroute. -/
theorem appendSuccessorSwapBothCrossCollisions_supportedByAdjacentSelectedRailPieces
    (firstSecondFace secondFirstFace : SelectedFace (web := web))
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
    AssemblySupportedByAdjacentSelectedRailPieces (successor := successor)
      (left := left)
      (appendSuccessorSwapBothCrossCollisions successor left
        firstSecondFace secondFirstFace hfirstSecondOld hfirstSecondNew
        hsecondFirstOld hsecondFirstNew hfirstFirst hsecondSecond) := by
  constructor
  · intro face hface
    let reroute :=
      SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
        (successor := successor) (left := left) firstSecondFace
          hfirstSecondOld hfirstSecondNew
    rcases reroute.route_support_subset face hface with hold | hnew
    · exact Or.inr (Or.inl hold)
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (List.mem_of_mem_tail hnew))))
  · intro face hface
    let reroute :=
      SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
        (successor := successor) (left := left) secondFirstFace
          hsecondFirstOld hsecondFirstNew
    rcases reroute.route_support_subset face hface with hold | hnew
    · exact Or.inr (Or.inr (Or.inl hold))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (List.mem_of_mem_tail hnew))))

/-- Exact provenance predicate on the first exhaustive classifier. -/
def SelectedLocalRailAppendOutcome.HasExactWindowProvenance
    (result : SelectedLocalRailAppendOutcome successor left) : Prop :=
  match result with
  | .straight assembly =>
      AssemblySupportedByAdjacentSelectedRailPieces (successor := successor)
        (left := left) assembly
  | .swapped assembly =>
      AssemblySupportedByAdjacentSelectedRailPieces (successor := successor)
        (left := left) assembly
  | .singleFirstSecond _ _ => True
  | .singleSecondFirst _ _ => True
  | .doubleCrossSameTrack _ _ _ => True

theorem classifyLocalSuccessorAppend_hasExactWindowProvenance :
    (classifyLocalSuccessorAppend successor left).HasExactWindowProvenance := by
  classical
  unfold classifyLocalSuccessorAppend
  split
  · rename_i hfirstSecond
    split
    · rename_i hsecondFirst
      exact appendSuccessorBypass_supportedByAdjacentSelectedRailPieces
        hfirstSecond hsecondFirst
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
          exact
            appendSuccessorSwapBothCrossCollisions_supportedByAdjacentSelectedRailPieces
              (SelectedRailSupportCollision.of_not_disjoint hfirstSecond).face
              (SelectedRailSupportCollision.of_not_disjoint hsecondFirst).face
              (SelectedRailSupportCollision.of_not_disjoint hfirstSecond).mem_old
              (SelectedRailSupportCollision.of_not_disjoint hfirstSecond).mem_new
              (SelectedRailSupportCollision.of_not_disjoint hsecondFirst).mem_old
              (SelectedRailSupportCollision.of_not_disjoint hsecondFirst).mem_new
              hfirstFirst hsecondSecond
        · trivial
      · trivial

/-- Exact predicate for the first centre-bridge classifier. -/
def SingleFirstSecondCenterBridgeOutcome.HasExactWindowProvenance
    {collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail}
    (result : SingleFirstSecondCenterBridgeOutcome collision) : Prop :=
  match result with
  | .assembly value =>
      AssemblySupportedByAdjacentSelectedRailPieces (successor := successor)
        (left := left) value
  | .meetsOldSecond _ => True
  | .meetsNewFirst _ => True
  | .containsLeftCenter _ => True

theorem classifySingleFirstSecondCenterBridge_hasExactWindowProvenance
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.firstRail.support successor.secondContinuation.support.tail) :
    (classifySingleFirstSecondCenterBridge collision).HasExactWindowProvenance := by
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
        exact appendSingleFirstSecondViaLeftCenter_supportContained
          collision holdSecond hnewFirst hcenter
    · trivial
  · trivial

/-- Exact predicate for the symmetric centre-bridge classifier. -/
def SingleSecondFirstCenterBridgeOutcome.HasExactWindowProvenance
    {collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail}
    (result : SingleSecondFirstCenterBridgeOutcome collision) : Prop :=
  match result with
  | .assembly value =>
      AssemblySupportedByAdjacentSelectedRailPieces (successor := successor)
        (left := left) value
  | .meetsOldFirst _ => True
  | .meetsNewSecond _ => True
  | .containsLeftCenter _ => True

theorem classifySingleSecondFirstCenterBridge_hasExactWindowProvenance
    (collision : SelectedRailSupportCollision (web := web)
      left.paths.secondRail.support successor.firstContinuation.support.tail) :
    (classifySingleSecondFirstCenterBridge collision).HasExactWindowProvenance := by
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
        exact appendSingleSecondFirstViaLeftCenter_supportContained
          collision holdFirst hnewSecond hcenter
    · trivial
  · trivial

/-- Exact provenance after the impossible mixed double-cross branch is
removed. -/
def SelectedLocalRailAppendResolvedOutcome.HasExactWindowProvenance
    (result : SelectedLocalRailAppendResolvedOutcome successor left) : Prop :=
  match result with
  | .straight assembly =>
      AssemblySupportedByAdjacentSelectedRailPieces (successor := successor)
        (left := left) assembly
  | .swapped assembly =>
      AssemblySupportedByAdjacentSelectedRailPieces (successor := successor)
        (left := left) assembly
  | .singleFirstSecond _ _ => True
  | .singleSecondFirst _ _ => True

theorem classifyLocalSuccessorAppendResolved_hasExactWindowProvenance :
    (classifyLocalSuccessorAppendResolved successor left).HasExactWindowProvenance := by
  classical
  have hbase := classifyLocalSuccessorAppend_hasExactWindowProvenance
    (successor := successor) (left := left)
  cases hresult : classifyLocalSuccessorAppend successor left with
  | straight assembly =>
      simpa [classifyLocalSuccessorAppendResolved, hresult,
        SelectedLocalRailAppendOutcome.HasExactWindowProvenance,
        SelectedLocalRailAppendResolvedOutcome.HasExactWindowProvenance] using hbase
  | swapped assembly =>
      simpa [classifyLocalSuccessorAppendResolved, hresult,
        SelectedLocalRailAppendOutcome.HasExactWindowProvenance,
        SelectedLocalRailAppendResolvedOutcome.HasExactWindowProvenance] using hbase
  | singleFirstSecond _ _ =>
      simp [classifyLocalSuccessorAppendResolved, hresult,
        SelectedLocalRailAppendResolvedOutcome.HasExactWindowProvenance]
  | singleSecondFirst _ _ =>
      simp [classifyLocalSuccessorAppendResolved, hresult,
        SelectedLocalRailAppendResolvedOutcome.HasExactWindowProvenance]
  | doubleCrossSameTrack firstSecond secondFirst sameTrack =>
      exact False.elim
        (not_doubleCrossSameTrack firstSecond secondFirst sameTrack)

/-- Exact provenance on the final finite length classifier. -/
def SelectedLocalRailAppendLengthResolvedOutcome.HasExactWindowProvenance
    (result : SelectedLocalRailAppendLengthResolvedOutcome successor left) : Prop :=
  match result with
  | .straight assembly =>
      AssemblySupportedByAdjacentSelectedRailPieces (successor := successor)
        (left := left) assembly
  | .swapped assembly =>
      AssemblySupportedByAdjacentSelectedRailPieces (successor := successor)
        (left := left) assembly
  | .firstSecondSameFirst _ _ _ => True
  | .firstSecondSameSecond _ _ _ => True
  | .firstSecondCenter _ _ _ => True
  | .secondFirstSameFirst _ _ _ => True
  | .secondFirstSameSecond _ _ _ => True
  | .secondFirstCenter _ _ _ => True

theorem classifyLocalSuccessorAppendLengthResolved_hasExactWindowProvenance :
    (classifyLocalSuccessorAppendLengthResolved successor left)
      |>.HasExactWindowProvenance := by
  classical
  have hresolved := classifyLocalSuccessorAppendResolved_hasExactWindowProvenance
    (successor := successor) (left := left)
  cases hresult : classifyLocalSuccessorAppendResolved successor left with
  | straight assembly =>
      simpa [classifyLocalSuccessorAppendLengthResolved, hresult,
        SelectedLocalRailAppendResolvedOutcome.HasExactWindowProvenance,
        SelectedLocalRailAppendLengthResolvedOutcome.HasExactWindowProvenance]
        using hresolved
  | swapped assembly =>
      simpa [classifyLocalSuccessorAppendLengthResolved, hresult,
        SelectedLocalRailAppendResolvedOutcome.HasExactWindowProvenance,
        SelectedLocalRailAppendLengthResolvedOutcome.HasExactWindowProvenance]
        using hresolved
  | singleFirstSecond cross _ =>
      have hs := classifySingleFirstSecondCenterBridge_hasExactWindowProvenance cross
      cases hcenter : classifySingleFirstSecondCenterBridge cross with
      | assembly value =>
          simpa [classifyLocalSuccessorAppendLengthResolved, hresult, hcenter,
            SingleFirstSecondCenterBridgeOutcome.HasExactWindowProvenance,
            SelectedLocalRailAppendLengthResolvedOutcome.HasExactWindowProvenance]
            using hs
      | meetsOldSecond _ => simp [classifyLocalSuccessorAppendLengthResolved,
          hresult, hcenter,
          SelectedLocalRailAppendLengthResolvedOutcome.HasExactWindowProvenance]
      | meetsNewFirst _ => simp [classifyLocalSuccessorAppendLengthResolved,
          hresult, hcenter,
          SelectedLocalRailAppendLengthResolvedOutcome.HasExactWindowProvenance]
      | containsLeftCenter _ => simp [classifyLocalSuccessorAppendLengthResolved,
          hresult, hcenter,
          SelectedLocalRailAppendLengthResolvedOutcome.HasExactWindowProvenance]
  | singleSecondFirst cross _ =>
      have hs := classifySingleSecondFirstCenterBridge_hasExactWindowProvenance cross
      cases hcenter : classifySingleSecondFirstCenterBridge cross with
      | assembly value =>
          simpa [classifyLocalSuccessorAppendLengthResolved, hresult, hcenter,
            SingleSecondFirstCenterBridgeOutcome.HasExactWindowProvenance,
            SelectedLocalRailAppendLengthResolvedOutcome.HasExactWindowProvenance]
            using hs
      | meetsOldFirst _ => simp [classifyLocalSuccessorAppendLengthResolved,
          hresult, hcenter,
          SelectedLocalRailAppendLengthResolvedOutcome.HasExactWindowProvenance]
      | meetsNewSecond _ => simp [classifyLocalSuccessorAppendLengthResolved,
          hresult, hcenter,
          SelectedLocalRailAppendLengthResolvedOutcome.HasExactWindowProvenance]
      | containsLeftCenter _ => simp [classifyLocalSuccessorAppendLengthResolved,
          hresult, hcenter,
          SelectedLocalRailAppendLengthResolvedOutcome.HasExactWindowProvenance]

/-- **L1 exact complete adjacent provenance.** Every constructive branch of
the unconditional adjacent append stays inside the five literal source
pieces, before that information is coarsened to two-centre proximity. -/
theorem appendLocalSuccessorComplete_hasExactWindowProvenance :
    (appendLocalSuccessorComplete successor left).HasExactWindowProvenance := by
  classical
  have hlength :=
    classifyLocalSuccessorAppendLengthResolved_hasExactWindowProvenance
      (successor := successor) (left := left)
  cases hresult : classifyLocalSuccessorAppendLengthResolved successor left with
  | straight assembly =>
      simpa [appendLocalSuccessorComplete, hresult,
        SelectedLocalRailAppendLengthResolvedOutcome.HasExactWindowProvenance,
        SelectedLocalRailAppendCompleteOutcome.HasExactWindowProvenance] using hlength
  | swapped assembly =>
      simpa [appendLocalSuccessorComplete, hresult,
        SelectedLocalRailAppendLengthResolvedOutcome.HasExactWindowProvenance,
        SelectedLocalRailAppendCompleteOutcome.HasExactWindowProvenance] using hlength
  | firstSecondSameFirst cross same lengths =>
      have hs := appendFirstSecondSameFirst_supportContained cross same lengths
      cases hrepair : appendFirstSecondSameFirst cross same lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumSupportedByAdjacentSelectedRailPieces,
          SelectedLocalRailAppendCompleteOutcome.HasExactWindowProvenance] using hs
  | firstSecondSameSecond cross same lengths =>
      have hs := appendFirstSecondSameSecond_supportContained cross same lengths
      cases hrepair : appendFirstSecondSameSecond cross same lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumSupportedByAdjacentSelectedRailPieces,
          SelectedLocalRailAppendCompleteOutcome.HasExactWindowProvenance] using hs
  | firstSecondCenter cross center lengths =>
      have hs := appendFirstSecondCenter_supportContained cross center lengths
      cases hrepair : appendFirstSecondCenter cross center lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumSupportedByAdjacentSelectedRailPieces,
          SelectedLocalRailAppendCompleteOutcome.HasExactWindowProvenance] using hs
  | secondFirstSameFirst cross same lengths =>
      have hs := appendSecondFirstSameFirst_supportContained cross same lengths
      cases hrepair : appendSecondFirstSameFirst cross same lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumSupportedByAdjacentSelectedRailPieces,
          SelectedLocalRailAppendCompleteOutcome.HasExactWindowProvenance] using hs
  | secondFirstSameSecond cross same lengths =>
      have hs := appendSecondFirstSameSecond_supportContained cross same lengths
      cases hrepair : appendSecondFirstSameSecond cross same lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumSupportedByAdjacentSelectedRailPieces,
          SelectedLocalRailAppendCompleteOutcome.HasExactWindowProvenance] using hs
  | secondFirstCenter cross center lengths =>
      have hs := appendSecondFirstCenter_supportContained cross center lengths
      cases hrepair : appendSecondFirstCenter cross center lengths <;>
        simpa [appendLocalSuccessorComplete, hresult, hrepair,
          AssemblySumSupportedByAdjacentSelectedRailPieces,
          SelectedLocalRailAppendCompleteOutcome.HasExactWindowProvenance] using hs

/-- Exact provenance implies the coarser two-centre certificate consumed by
remote separation. -/
theorem SelectedLocalRailAppendCompleteOutcome.HasExactWindowProvenance.toWindowProvenance
    {result : SelectedLocalRailAppendCompleteOutcome successor left}
    (hexact : result.HasExactWindowProvenance) :
    result.HasWindowProvenance (corridor := corridor) := by
  cases result with
  | straight assembly | swapped assembly =>
      exact supportedBySelectedCenterPair_of_support_subset_adjacentPieces
        assembly hexact.1 hexact.2

/-- A complete adjacent outcome retaining the exact literal five-piece
support certificate. -/
structure ExactCertifiedSelectedLocalRailTerminalWindow
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) where
  outcome : SelectedLocalRailAppendCompleteOutcome successor left
  hasExactWindowProvenance : outcome.HasExactWindowProvenance

/-- The canonical exact terminal window supplied by the complete adjacent
classifier. -/
noncomputable def ExactCertifiedSelectedLocalRailTerminalWindow.ofComplete :
    ExactCertifiedSelectedLocalRailTerminalWindow successor left :=
  ⟨appendLocalSuccessorComplete successor left,
    appendLocalSuccessorComplete_hasExactWindowProvenance⟩

/-- Forget only the exact source-piece refinement, retaining the earlier
two-centre terminal-window API. -/
def ExactCertifiedSelectedLocalRailTerminalWindow.toCertified
    (window : ExactCertifiedSelectedLocalRailTerminalWindow successor left) :
    CertifiedSelectedLocalRailTerminalWindow successor left :=
  ⟨window.outcome, window.hasExactWindowProvenance.toWindowProvenance⟩

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
