import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementFutureSeparation
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailFrozenInteriorPrepend

/-!
# L1: prepend a frozen prefix to an exact middle replacement

The canonical four-cell middle replacement rebuilds both live rails together.
Its source-support receipt locates every surviving face in one of three
literal two-centre packets.  A sufficiently old prefix is therefore disjoint
from the complete repaired support, even though the repaired support does not
fit inside one two-centre window.

This file joins that local fact to the interface-aware rolling invariant.
Successful straight and swapped replacements are appended to the frozen
prefix and advance its cutoff to the third centre.  The exact collision branch
is returned unchanged.  No centre-avoidance hypothesis is added.

This is one bounded rolling step.  It does not eliminate the collision branch,
iterate the step to arbitrary corridor length, attach either end cap, construct
the final dual crosscuts, or close Fable flag L1.
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

private theorem frozenSupport_disjoint_of_middleReplacementPieces
    {cutoff : Nat} {frozenSupport support : List (SelectedFace (web := web))}
    (hfrozen : SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor) cutoff frozenSupport)
    (hgap : cutoff + 3 < firstInterior.center.val)
    {middleFirstFinish middleSecondFinish : SelectedFace (web := web)}
    (middle : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftBefore)
      (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftAfter)
      middleFirstFinish middleSecondFinish)
    (hmiddle : SupportedBySelectedCenterPair (corridor := corridor) middle
      (SecondInterior (firstInterior := firstInterior)
        (hfirstNext := hfirstNext)).center
      (ThirdInterior (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center)
    (hcontained : ∀ face ∈ support,
      FaceInMiddleReplacementSplicePieces
        (bridge := bridge) (lastSuccessor := lastSuccessor)
        (firstLeft := firstLeft) middle face) :
    frozenSupport.Disjoint support := by
  rw [List.disjoint_left]
  intro face hfrozenFace hsupportFace
  have exclude
      {leftInterior : CorridorInterior blockLength}
      {hleftNext : leftInterior.center.val + 2 < blockLength}
      (hnear : FaceNearSelectedCenterPair (corridor := corridor)
        leftInterior.center
        (nextCorridorInterior leftInterior hleftNext).center face)
      (hleftGap : cutoff + 3 < leftInterior.center.val) : False := by
    have hsingle : SupportNearSelectedCenterPair (corridor := corridor)
        leftInterior.center
        (nextCorridorInterior leftInterior hleftNext).center [face] := by
      intro current hcurrent
      have hcurrentEq : current = face := by simpa using hcurrent
      subst current
      exact hnear
    exact (List.disjoint_left.mp (hfrozen [face] hsingle hleftGap)
      hfrozenFace) (by simp)
  rcases hcontained face hsupportFace with
    hfirstFirst | hfirstSecond | hmiddleFirst | hmiddleSecond |
      hlastFirst | hlastSecond
  · exact exclude (leftInterior := firstInterior) (hleftNext := hfirstNext)
      (Or.inr (Or.inr (Or.inl
        (firstLeft.paths.firstRail_support_adjacent_center face hfirstFirst))))
      hgap
  · exact exclude (leftInterior := firstInterior) (hleftNext := hfirstNext)
      (Or.inr (Or.inr (Or.inl
        (firstLeft.paths.secondRail_support_adjacent_center face hfirstSecond))))
      hgap
  · exact exclude (leftInterior := SecondInterior (firstInterior := firstInterior)
      (hfirstNext := hfirstNext)) (hleftNext := hbridgeNext)
      (hmiddle.1 face hmiddleFirst) (by
        change cutoff + 3 < firstInterior.center.val + 1
        omega)
  · exact exclude (leftInterior := SecondInterior (firstInterior := firstInterior)
      (hfirstNext := hfirstNext)) (hleftNext := hbridgeNext)
      (hmiddle.2 face hmiddleSecond) (by
        change cutoff + 3 < firstInterior.center.val + 1
        omega)
  · rw [rebaseLastContinuation_firstRail_support] at hlastFirst
    have hlastFirst' :
        face ∈ lastSuccessor.rightRails.paths.firstRail.support := by
      rw [← lastSuccessor.firstContinuation_support]
      exact hlastFirst
    exact exclude (leftInterior := ThirdInterior (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext))
      (hleftNext := hlastNext)
      (Or.inr (Or.inr (Or.inr
        (lastSuccessor.rightRails.paths.firstRail_support_adjacent_center
          face hlastFirst')))) (by
            change cutoff + 3 < firstInterior.center.val + 2
            omega)
  · rw [rebaseLastContinuation_secondRail_support] at hlastSecond
    have hlastSecond' :
        face ∈ lastSuccessor.rightRails.paths.secondRail.support := by
      rw [← lastSuccessor.secondContinuation_support]
      exact hlastSecond
    exact exclude (leftInterior := ThirdInterior (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext))
      (hleftNext := hlastNext)
      (Or.inr (Or.inr (Or.inr
        (lastSuccessor.rightRails.paths.secondRail_support_adjacent_center
          face hlastSecond')))) (by
            change cutoff + 3 < firstInterior.center.val + 2
            omega)

namespace ExactSelectedLocalRailMiddleReplacementOutcome

/-- Result of attaching an exact middle replacement to an older
interior-frozen prefix.  The collision constructor retains the original exact
collision witness. -/
inductive InteriorFrozenPrependOutcome
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (firstSuccessor.rightRailsAsNextLeft bridge)}
    {firstStart secondStart : SelectedFace (web := web)}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter))
    (outcome : ExactSelectedLocalRailMiddleReplacementOutcome
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace) : Type (u + 1)
  | straight
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        firstStart secondStart
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingBefore)
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingAfter))
      (interiorSeparated : InteriorSeparatedFromFutureSelectedWindows
        (corridor := corridor) assembly
        (ThirdInterior (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center.val)
  | swapped
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        firstStart secondStart
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingAfter)
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingBefore))
      (interiorSeparated : InteriorSeparatedFromFutureSelectedWindows
        (corridor := corridor) assembly
        (ThirdInterior (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center.val)
  | collision
      (face : SelectedFace (web := web))
      (data : ExactSelectedLocalRailMiddleReplacementCollision
        (firstSuccessor := firstSuccessor) (bridge := bridge)
        (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face)

/-- **L1 exact rolling step.** Attach an old interior-frozen prefix to a
successful simultaneous four-cell repair, advancing the cutoff to the third
centre.  Failure returns the exact collision unchanged. -/
noncomputable def prependInteriorFrozen
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (firstSuccessor.rightRailsAsNextLeft bridge)}
    {firstStart secondStart : SelectedFace (web := web)}
    {cutoff : Nat}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter))
    (outcome : ExactSelectedLocalRailMiddleReplacementOutcome
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace)
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (hprefix : InteriorSeparatedFromFutureSelectedWindows
      (corridor := corridor) prefixAssembly cutoff)
    (hgap : cutoff + 3 < firstInterior.center.val) :
    outcome.InteriorFrozenPrependOutcome prefixAssembly := by
  have hfuture := outcome.hasFutureSeparation hsource
  have hprovenance := outcome.hasSourceSupportProvenance
  have hmiddleProvenance : trace.toOutcome.HasWindowProvenance
      (corridor := corridor) := by
    rw [trace.toOutcome_eq_complete]
    exact appendLocalSuccessorComplete_hasWindowProvenance
  cases outcome with
  | straight middle hresult prefixMiddle hleft suffixAssembly hright =>
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
      have hfirstFirst := frozenSupport_disjoint_of_middleReplacementPieces
        (firstSuccessor := firstSuccessor) (bridge := bridge)
        (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
        hprefix.1 hgap _ hmiddleRebased hprovenance.1
      have hsecondSecond := frozenSupport_disjoint_of_middleReplacementPieces
        (firstSuccessor := firstSuccessor) (bridge := bridge)
        (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
        hprefix.2 hgap _ hmiddleRebased hprovenance.2
      have hfirstSecond := frozenSupport_disjoint_of_middleReplacementPieces
        (firstSuccessor := firstSuccessor) (bridge := bridge)
        (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
        hprefix.1 hgap _ hmiddleRebased hprovenance.2
      have hsecondFirst := frozenSupport_disjoint_of_middleReplacementPieces
        (firstSuccessor := firstSuccessor) (bridge := bridge)
        (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
        hprefix.2 hgap _ hmiddleRebased hprovenance.1
      have hfirstEndNotSecondTail :
          selectedPlacementSideFace firstPlacement firstIncomingBefore ∉
            suffixAssembly.secondRail.support.tail := by
        intro hmem
        exact (List.disjoint_left.mp
          suffixAssembly.firstRail_support_disjoint_secondRail
          suffixAssembly.firstRail.start_mem_support)
          (List.mem_of_mem_tail hmem)
      have hsecondEndNotFirstTail :
          selectedPlacementSideFace firstPlacement firstIncomingAfter ∉
            suffixAssembly.firstRail.support.tail := by
        intro hmem
        exact (List.disjoint_left.mp
          suffixAssembly.firstRail_support_disjoint_secondRail
          (List.mem_of_mem_tail hmem))
          suffixAssembly.secondRail.start_mem_support
      have hfirstPath := walk_support_disjoint_tail_of_dropLast_disjoint
        prefixAssembly.firstRail suffixAssembly.firstRail
        suffixAssembly.firstRail_isPath hfirstFirst
      have hsecondPath := walk_support_disjoint_tail_of_dropLast_disjoint
        prefixAssembly.secondRail suffixAssembly.secondRail
        suffixAssembly.secondRail_isPath hsecondSecond
      have hfirstSecondTail :=
        walk_support_disjoint_tail_of_dropLast_disjoint_of_end_not_mem
          prefixAssembly.firstRail suffixAssembly.secondRail
          hfirstSecond hfirstEndNotSecondTail
      have hsecondFirstTail :=
        walk_support_disjoint_tail_of_dropLast_disjoint_of_end_not_mem
          prefixAssembly.secondRail suffixAssembly.firstRail
          hsecondFirst hsecondEndNotFirstTail
      have hfutureInterior : InteriorSeparatedFromFutureSelectedWindows
          (corridor := corridor) suffixAssembly
          (ThirdInterior (firstInterior := firstInterior)
            (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center.val :=
        ⟨supportSeparatedFromFutureSelectedWindows_dropLast hfuture.1,
          supportSeparatedFromFutureSelectedWindows_dropLast hfuture.2⟩
      let assembly := appendAssembly prefixAssembly suffixAssembly
        hfirstPath hsecondPath hfirstSecondTail hsecondFirstTail
      exact .straight assembly
        (appendAssembly_interiorSeparatedFromFuture prefixAssembly suffixAssembly
          hfirstPath hsecondPath hfirstSecondTail hsecondFirstTail
          hprefix hfutureInterior (by
            change cutoff ≤ firstInterior.center.val + 2
            omega))
  | swapped middle hresult prefixMiddle hleft suffixAssembly hright =>
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
      have hfirstFirst := frozenSupport_disjoint_of_middleReplacementPieces
        (firstSuccessor := firstSuccessor) (bridge := bridge)
        (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
        hprefix.1 hgap _ hmiddleRebased hprovenance.1
      have hsecondSecond := frozenSupport_disjoint_of_middleReplacementPieces
        (firstSuccessor := firstSuccessor) (bridge := bridge)
        (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
        hprefix.2 hgap _ hmiddleRebased hprovenance.2
      have hfirstSecond := frozenSupport_disjoint_of_middleReplacementPieces
        (firstSuccessor := firstSuccessor) (bridge := bridge)
        (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
        hprefix.1 hgap _ hmiddleRebased hprovenance.2
      have hsecondFirst := frozenSupport_disjoint_of_middleReplacementPieces
        (firstSuccessor := firstSuccessor) (bridge := bridge)
        (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
        hprefix.2 hgap _ hmiddleRebased hprovenance.1
      have hfirstEndNotSecondTail :
          selectedPlacementSideFace firstPlacement firstIncomingBefore ∉
            suffixAssembly.secondRail.support.tail := by
        intro hmem
        exact (List.disjoint_left.mp
          suffixAssembly.firstRail_support_disjoint_secondRail
          suffixAssembly.firstRail.start_mem_support)
          (List.mem_of_mem_tail hmem)
      have hsecondEndNotFirstTail :
          selectedPlacementSideFace firstPlacement firstIncomingAfter ∉
            suffixAssembly.firstRail.support.tail := by
        intro hmem
        exact (List.disjoint_left.mp
          suffixAssembly.firstRail_support_disjoint_secondRail
          (List.mem_of_mem_tail hmem))
          suffixAssembly.secondRail.start_mem_support
      have hfirstPath := walk_support_disjoint_tail_of_dropLast_disjoint
        prefixAssembly.firstRail suffixAssembly.firstRail
        suffixAssembly.firstRail_isPath hfirstFirst
      have hsecondPath := walk_support_disjoint_tail_of_dropLast_disjoint
        prefixAssembly.secondRail suffixAssembly.secondRail
        suffixAssembly.secondRail_isPath hsecondSecond
      have hfirstSecondTail :=
        walk_support_disjoint_tail_of_dropLast_disjoint_of_end_not_mem
          prefixAssembly.firstRail suffixAssembly.secondRail
          hfirstSecond hfirstEndNotSecondTail
      have hsecondFirstTail :=
        walk_support_disjoint_tail_of_dropLast_disjoint_of_end_not_mem
          prefixAssembly.secondRail suffixAssembly.firstRail
          hsecondFirst hsecondEndNotFirstTail
      have hfutureInterior : InteriorSeparatedFromFutureSelectedWindows
          (corridor := corridor) suffixAssembly
          (ThirdInterior (firstInterior := firstInterior)
            (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center.val :=
        ⟨supportSeparatedFromFutureSelectedWindows_dropLast hfuture.1,
          supportSeparatedFromFutureSelectedWindows_dropLast hfuture.2⟩
      let assembly := appendAssembly prefixAssembly suffixAssembly
        hfirstPath hsecondPath hfirstSecondTail hsecondFirstTail
      exact .swapped assembly
        (appendAssembly_interiorSeparatedFromFuture prefixAssembly suffixAssembly
          hfirstPath hsecondPath hfirstSecondTail hsecondFirstTail
          hprefix hfutureInterior (by
            change cutoff ≤ firstInterior.center.val + 2
            omega))
  | collision face data => exact .collision face data

end ExactSelectedLocalRailMiddleReplacementOutcome

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
