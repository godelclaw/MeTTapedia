import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacement
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailFrozenPrefixSeparation
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailWindowSeparation

/-!
# L1: future separation of a successful middle replacement

The canonical four-cell middle replacement rebuilds both rails at once.  Its
source-support receipt says that every surviving face belongs to one of three
literal packets: the first local pair, the repaired middle pair, or the last
continuation pair.  Each packet lies in an adjacent two-centre window, so the
already-proved remote-window theorem separates it from every sufficiently
later selected window.

This file records that consequence on the replacement outcome.  Successful
straight and swapped branches carry full future separation at the third
centre; the exact collision branch remains explicitly fail-closed.  This is a
rolling-window receipt, not an elimination of the collision branch, an
arbitrary-length construction, either end cap, or closure of Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
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
    {firstInterior : CorridorInterior blockLength}
    {hfirstNext : firstInterior.center.val + 2 < blockLength}
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {hlastNext :
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center.val +
          2 < blockLength}
    {firstPlacement : SelectedInternalHexRungPlacement corridor rungs firstInterior}
    {secondPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior firstInterior hfirstNext)}
    {thirdPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)}
    {fourthPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext)}
    {firstSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfirstNext
      firstPlacement secondPlacement}
    {bridge : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement}
    {lastSuccessor : SeparatedSelectedSourceLocalRailSuccessor hlastNext
      thirdPlacement fourthPlacement}
    {firstIncomingBefore firstIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions firstPlacement}}
    {firstLeft : SeparatedSelectedSourceLocalRailPaths firstPlacement
      firstIncomingBefore firstIncomingAfter firstSuccessor.frame.leftBefore
      firstSuccessor.frame.leftAfter}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SecondInterior :=
  nextCorridorInterior firstInterior hfirstNext

private abbrev ThirdInterior :=
  nextCorridorInterior
    (nextCorridorInterior firstInterior hfirstNext) hbridgeNext

private theorem face_not_mem_future_of_near_window
    {leftInterior : CorridorInterior blockLength}
    {hleftNext : leftInterior.center.val + 2 < blockLength}
    {futureInterior : CorridorInterior blockLength}
    {hfutureNext : futureInterior.center.val + 2 < blockLength}
    {face : SelectedFace (web := web)}
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (futureSupport : List (SelectedFace (web := web)))
    (hface : FaceNearSelectedCenterPair (corridor := corridor)
      leftInterior.center (nextCorridorInterior leftInterior hleftNext).center face)
    (hfuture : SupportNearSelectedCenterPair (corridor := corridor)
      futureInterior.center
      (nextCorridorInterior futureInterior hfutureNext).center futureSupport)
    (hgap : leftInterior.center.val + 3 < futureInterior.center.val) :
    face ∉ futureSupport := by
  have hsingle : SupportNearSelectedCenterPair (corridor := corridor)
      leftInterior.center (nextCorridorInterior leftInterior hleftNext).center
      [face] := by
    intro current hcurrent
    have hcurrentEq : current = face := by simpa using hcurrent
    subst current
    exact hface
  have hdisjoint :=
    supports_disjoint_of_near_selected_center_pairs_of_add_three_lt
      hsource [face] futureSupport hsingle hfuture hgap
  intro hmem
  exact (List.disjoint_left.mp hdisjoint (by simp)) hmem

private theorem supportSeparatedFromFuture_of_middleReplacementPieces
    {middleFirstFinish middleSecondFinish : SelectedFace (web := web)}
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (middle : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftBefore)
      (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftAfter)
      middleFirstFinish middleSecondFinish)
    (hmiddle : SupportedBySelectedCenterPair (corridor := corridor) middle
      (SecondInterior (firstInterior := firstInterior)
        (hfirstNext := hfirstNext)).center
      (ThirdInterior (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center)
    {support : List (SelectedFace (web := web))}
    (hcontained : ∀ face ∈ support,
      FaceInMiddleReplacementSplicePieces
        (bridge := bridge) (lastSuccessor := lastSuccessor)
        (firstLeft := firstLeft) middle face) :
    SupportSeparatedFromFutureSelectedWindows (corridor := corridor)
      (ThirdInterior (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center.val
      support := by
  intro futureInterior hfutureNext futureSupport hfuture hgap
  rw [List.disjoint_left]
  intro face hface hfutureFace
  rcases hcontained face hface with
    hfirstFirst | hfirstSecond | hmiddleFirst | hmiddleSecond |
      hlastFirst | hlastSecond
  · apply (face_not_mem_future_of_near_window hsource futureSupport
      (leftInterior := firstInterior) (hleftNext := hfirstNext)
      (Or.inr (Or.inr (Or.inl
        (firstLeft.paths.firstRail_support_adjacent_center face hfirstFirst))))
      hfuture (by
        change firstInterior.center.val + 2 + 3 < futureInterior.center.val at hgap
        omega)) hfutureFace
  · apply (face_not_mem_future_of_near_window hsource futureSupport
      (leftInterior := firstInterior) (hleftNext := hfirstNext)
      (Or.inr (Or.inr (Or.inl
        (firstLeft.paths.secondRail_support_adjacent_center face hfirstSecond))))
      hfuture (by
        change firstInterior.center.val + 2 + 3 < futureInterior.center.val at hgap
        omega)) hfutureFace
  · apply (face_not_mem_future_of_near_window hsource futureSupport
      (leftInterior := SecondInterior (firstInterior := firstInterior)
        (hfirstNext := hfirstNext)) (hleftNext := hbridgeNext)
      (hmiddle.1 face hmiddleFirst) hfuture (by
        change firstInterior.center.val + 2 + 3 < futureInterior.center.val at hgap
        change firstInterior.center.val + 1 + 3 < futureInterior.center.val
        omega)) hfutureFace
  · apply (face_not_mem_future_of_near_window hsource futureSupport
      (leftInterior := SecondInterior (firstInterior := firstInterior)
        (hfirstNext := hfirstNext)) (hleftNext := hbridgeNext)
      (hmiddle.2 face hmiddleSecond) hfuture (by
        change firstInterior.center.val + 2 + 3 < futureInterior.center.val at hgap
        change firstInterior.center.val + 1 + 3 < futureInterior.center.val
        omega)) hfutureFace
  · rw [rebaseLastContinuation_firstRail_support] at hlastFirst
    have hlastFirst' :
        face ∈ lastSuccessor.rightRails.paths.firstRail.support := by
      rw [← lastSuccessor.firstContinuation_support]
      exact hlastFirst
    apply (face_not_mem_future_of_near_window hsource futureSupport
      (leftInterior := ThirdInterior (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext))
      (hleftNext := hlastNext)
      (Or.inr (Or.inr (Or.inr
        (lastSuccessor.rightRails.paths.firstRail_support_adjacent_center
          face hlastFirst')))) hfuture hgap) hfutureFace
  · rw [rebaseLastContinuation_secondRail_support] at hlastSecond
    have hlastSecond' :
        face ∈ lastSuccessor.rightRails.paths.secondRail.support := by
      rw [← lastSuccessor.secondContinuation_support]
      exact hlastSecond
    apply (face_not_mem_future_of_near_window hsource futureSupport
      (leftInterior := ThirdInterior (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext))
      (hleftNext := hlastNext)
      (Or.inr (Or.inr (Or.inr
        (lastSuccessor.rightRails.paths.secondRail_support_adjacent_center
          face hlastSecond')))) hfuture hgap) hfutureFace

/-- Future-separation predicate on the exact two-stage middle replacement.
Successful branches carry the full invariant; the exact collision branch
retains its witness and makes no success claim. -/
def ExactSelectedLocalRailMiddleReplacementOutcome.HasFutureSeparation
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (firstSuccessor.rightRailsAsNextLeft bridge)}
    (outcome : ExactSelectedLocalRailMiddleReplacementOutcome
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace) : Prop :=
  match outcome with
  | .straight _ _ _ _ assembly _ | .swapped _ _ _ _ assembly _ =>
      assembly.SeparatedFromFutureSelectedWindows (corridor := corridor)
        (ThirdInterior (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center.val
  | .collision _ _ => True

/-- **L1 middle-replacement future receipt.** Every successful result of the
actual two-stage replacement is separated from all sufficiently later selected
windows.  No new geometric premise is introduced. -/
theorem ExactSelectedLocalRailMiddleReplacementOutcome.hasFutureSeparation
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (firstSuccessor.rightRailsAsNextLeft bridge)}
    (outcome : ExactSelectedLocalRailMiddleReplacementOutcome
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace) :
    outcome.HasFutureSeparation := by
  have hprovenance := outcome.hasSourceSupportProvenance
  have hmiddleProvenance : trace.toOutcome.HasWindowProvenance
      (corridor := corridor) := by
    rw [trace.toOutcome_eq_complete]
    exact appendLocalSuccessorComplete_hasWindowProvenance
  cases outcome with
  | straight middle hresult prefixMiddle hleft assembly hright =>
      rw [hresult] at hmiddleProvenance
      change SupportedBySelectedCenterPair (corridor := corridor) middle
        (SecondInterior (firstInterior := firstInterior)
          (hfirstNext := hfirstNext)).center
        (ThirdInterior (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center
        at hmiddleProvenance
      have hmiddleRebased :=
        rebaseMiddleStraight_supportedBySelectedCenterPair middle
          hmiddleProvenance
      exact ⟨
        supportSeparatedFromFuture_of_middleReplacementPieces
          (firstSuccessor := firstSuccessor) (bridge := bridge)
          (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
          hsource _ hmiddleRebased hprovenance.1,
        supportSeparatedFromFuture_of_middleReplacementPieces
          (firstSuccessor := firstSuccessor) (bridge := bridge)
          (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
          hsource _ hmiddleRebased hprovenance.2⟩
  | swapped middle hresult prefixMiddle hleft assembly hright =>
      rw [hresult] at hmiddleProvenance
      change SupportedBySelectedCenterPair (corridor := corridor) middle
        (SecondInterior (firstInterior := firstInterior)
          (hfirstNext := hfirstNext)).center
        (ThirdInterior (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center
        at hmiddleProvenance
      have hmiddleRebased :=
        rebaseMiddleSwapped_supportedBySelectedCenterPair middle
          hmiddleProvenance
      exact ⟨
        supportSeparatedFromFuture_of_middleReplacementPieces
          (firstSuccessor := firstSuccessor) (bridge := bridge)
          (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
          hsource _ hmiddleRebased hprovenance.1,
        supportSeparatedFromFuture_of_middleReplacementPieces
          (firstSuccessor := firstSuccessor) (bridge := bridge)
          (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
          hsource _ hmiddleRebased hprovenance.2⟩
  | collision => trivial

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
