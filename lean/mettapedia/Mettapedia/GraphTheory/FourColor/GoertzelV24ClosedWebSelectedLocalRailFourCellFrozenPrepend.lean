import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailFourCellFutureSeparation
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailFrozenInteriorPrepend

/-!
# L1: prepend an interior-frozen prefix across a canonical four-cell window

This is the bounded rolling step exposed by the previous two receipts.  A
remote prefix freezes only the interiors of its two rails.  A canonical
four-cell transition supplies both support provenance and future separation.
When the transition succeeds, the prefix is appended to its two simple rails
and the advanced assembly again carries the interior-frozen invariant.  When
it collides, the exact collision-bearing transition is retained and no append
is claimed.

Thus the successful branch advances the corridor coordinate constructively;
the collision branch remains the live finite geometry.  This module does not
eliminate that branch, iterate to arbitrary length, attach either end cap, or
close Fable flag L1.
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

private abbrev ThirdInterior :=
  nextCorridorInterior
    (nextCorridorInterior firstInterior hfirstNext) hbridgeNext

/-- Predicate distinguishing the four exact collision constructors from the
two successful endpoint orders. -/
def ExactSelectedLocalRailFourCellRetainedOutcome.IsCollision
    {firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft}
    {lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (bridge.rightRailsAsNextLeft lastSuccessor)}
    (outcome : ExactSelectedLocalRailFourCellRetainedOutcome
      firstWindow lastWindow) : Prop :=
  match outcome with
  | .straight _ | .swapped _ => False
  | .straightStraightCollision _ _ _ _ _
  | .straightSwappedCollision _ _ _ _ _
  | .swappedStraightCollision _ _ _ _ _
  | .swappedSwappedCollision _ _ _ _ _ => True

private theorem frozenInterior_disjoint_of_window_pair_provenance
    {cutoff : Nat} {frozenSupport support : List (SelectedFace (web := web))}
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (bridge.rightRailsAsNextLeft lastSuccessor))
    (hfrozen : SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor) cutoff frozenSupport)
    (hgap : cutoff + 3 < firstInterior.center.val)
    (hprovenance : SupportContainedInExactTerminalWindowPair
      firstWindow lastWindow support) :
    frozenSupport.Disjoint support := by
  have hfirstFirst := hfrozen firstWindow.toCertified.firstSupport
    firstWindow.toCertified.firstSupport_near hgap
  have hfirstSecond := hfrozen firstWindow.toCertified.secondSupport
    firstWindow.toCertified.secondSupport_near hgap
  have hlastGap : cutoff + 3 <
      (ThirdInterior (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center.val := by
    change cutoff + 3 < firstInterior.center.val + 2
    omega
  have hlastFirst := hfrozen lastWindow.toCertified.firstSupport
    lastWindow.toCertified.firstSupport_near hlastGap
  have hlastSecond := hfrozen lastWindow.toCertified.secondSupport
    lastWindow.toCertified.secondSupport_near hlastGap
  rw [List.disjoint_left]
  intro face hfrozenFace hsupportFace
  rcases hprovenance face hsupportFace with
    hfirstFirstFace | hfirstSecondFace | hlastFirstFace | hlastSecondFace
  · exact (List.disjoint_left.mp hfirstFirst hfrozenFace) hfirstFirstFace
  · exact (List.disjoint_left.mp hfirstSecond hfrozenFace) hfirstSecondFace
  · exact (List.disjoint_left.mp hlastFirst hfrozenFace) hlastFirstFace
  · exact (List.disjoint_left.mp hlastSecond hfrozenFace) hlastSecondFace

private theorem walk_support_disjoint_tail_of_dropLast_disjoint_of_end_not_mem
    {F : Type*} {H : SimpleGraph F}
    {prefixStart prefixFinish suffixStart suffixFinish : F}
    (prefixWalk : H.Walk prefixStart prefixFinish)
    (suffix : H.Walk suffixStart suffixFinish)
    (hinterior : prefixWalk.support.dropLast.Disjoint suffix.support) :
    prefixFinish ∉ suffix.support.tail →
    prefixWalk.support.Disjoint suffix.support.tail := by
  intro hendNotMem
  rw [List.disjoint_left] at hinterior ⊢
  intro face hprefix hsuffixTail
  have hsplit : prefixWalk.support.dropLast ++ [prefixFinish] = prefixWalk.support := by
    simpa using List.dropLast_append_getLast prefixWalk.support_ne_nil
  rw [← hsplit] at hprefix
  rcases List.mem_append.mp hprefix with hdrop | hend
  · exact hinterior hdrop (List.mem_of_mem_tail hsuffixTail)
  · have hface : face = prefixFinish := by simpa using hend
    subst face
    exact hendNotMem hsuffixTail

private theorem walk_support_disjoint_tail_of_dropLast_disjoint
    {F : Type*} {H : SimpleGraph F} {start middle finish : F}
    (prefixWalk : H.Walk start middle) (suffix : H.Walk middle finish)
    (hsuffix : suffix.IsPath)
    (hinterior : prefixWalk.support.dropLast.Disjoint suffix.support) :
    prefixWalk.support.Disjoint suffix.support.tail := by
  apply walk_support_disjoint_tail_of_dropLast_disjoint_of_end_not_mem
    prefixWalk suffix hinterior
  have hnodup := hsuffix.support_nodup
  rw [← suffix.cons_tail_support] at hnodup
  exact (List.nodup_cons.mp hnodup).1

private theorem dropLast_append_of_right_ne_nil
    {A : Type*} (left right : List A) (hright : right ≠ []) :
    (left ++ right).dropLast = left ++ right.dropLast := by
  induction left with
  | nil => simp
  | cons head tail ih =>
      have htail : tail ++ right ≠ [] :=
        List.append_ne_nil_of_right_ne_nil tail hright
      rw [List.cons_append, List.dropLast_cons_of_ne_nil htail, ih]
      rfl

private theorem append_interiorSeparatedFromFuture
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {oldCutoff newCutoff : Nat}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (suffixAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish)
    (hfirstPath : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.firstRail.support.tail)
    (hsecondPath : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.secondRail.support.tail)
    (hfirstSecond : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.secondRail.support.tail)
    (hsecondFirst : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.firstRail.support.tail)
    (hprefix : InteriorSeparatedFromFutureSelectedWindows
      (corridor := corridor) prefixAssembly oldCutoff)
    (hsuffix : suffixAssembly.SeparatedFromFutureSelectedWindows
      (corridor := corridor) newCutoff)
    (hle : oldCutoff ≤ newCutoff) :
    InteriorSeparatedFromFutureSelectedWindows (corridor := corridor)
      (appendAssembly prefixAssembly suffixAssembly hfirstPath hsecondPath
        hfirstSecond hsecondFirst) newCutoff := by
  constructor
  · change SupportSeparatedFromFutureSelectedWindows (corridor := corridor)
      newCutoff
      (prefixAssembly.firstRail.append suffixAssembly.firstRail).support.dropLast
    rw [SimpleGraph.Walk.support_append_eq_support_dropLast_append,
      dropLast_append_of_right_ne_nil _ _ suffixAssembly.firstRail.support_ne_nil]
    exact supportSeparatedFromFutureSelectedWindows_append
      (SupportSeparatedFromFutureSelectedWindows.mono hprefix.1 hle)
      (supportSeparatedFromFutureSelectedWindows_dropLast hsuffix.1)
  · change SupportSeparatedFromFutureSelectedWindows (corridor := corridor)
      newCutoff
      (prefixAssembly.secondRail.append suffixAssembly.secondRail).support.dropLast
    rw [SimpleGraph.Walk.support_append_eq_support_dropLast_append,
      dropLast_append_of_right_ne_nil _ _ suffixAssembly.secondRail.support_ne_nil]
    exact supportSeparatedFromFutureSelectedWindows_append
      (SupportSeparatedFromFutureSelectedWindows.mono hprefix.2 hle)
      (supportSeparatedFromFutureSelectedWindows_dropLast hsuffix.2)

namespace SupportCertifiedExactSelectedLocalRailTracedFourCellTransition

/-- Result of applying a canonical four-cell transition to an older
interior-frozen prefix.  The collision constructor retains the original
transition, whose outcome contains the exact collision witness. -/
inductive InteriorFrozenPrependOutcome
    {firstStart secondStart : SelectedFace (web := web)}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter))
    (transition : SupportCertifiedExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)) : Type (u + 1)
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
  | collision (hcollision : transition.transition.outcome.IsCollision)

/-- **L1 bounded rolling step.** Prepend an interior-frozen remote prefix to
the canonical four-cell output.  Success advances the endpoint and cutoff;
failure retains the exact collision branch rather than assuming it away. -/
noncomputable def
    prependInteriorFrozen
    {firstStart secondStart : SelectedFace (web := web)}
    {cutoff : Nat}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter))
    (transition : SupportCertifiedExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft))
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (hprefix : InteriorSeparatedFromFutureSelectedWindows
      (corridor := corridor) prefixAssembly cutoff)
    (hgap : cutoff + 3 < firstInterior.center.val) :
    transition.InteriorFrozenPrependOutcome prefixAssembly := by
  have hfuture := transition.hasFutureSeparation hsource
  have hprovenance := transition.hasWindowSupportProvenance
  cases hresult : transition.transition.outcome with
  | straight suffixAssembly =>
      rw [hresult] at hfuture hprovenance
      change suffixAssembly.SeparatedFromFutureSelectedWindows
        (corridor := corridor)
        (ThirdInterior (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center.val
        at hfuture
      have hfirstFirst := frozenInterior_disjoint_of_window_pair_provenance
        transition.transition.firstTrace.toExactTerminalWindow
        transition.transition.lastTrace.toExactTerminalWindow
        hprefix.1 hgap hprovenance.1
      have hsecondSecond := frozenInterior_disjoint_of_window_pair_provenance
        transition.transition.firstTrace.toExactTerminalWindow
        transition.transition.lastTrace.toExactTerminalWindow
        hprefix.2 hgap hprovenance.2
      have hfirstSecond := frozenInterior_disjoint_of_window_pair_provenance
        transition.transition.firstTrace.toExactTerminalWindow
        transition.transition.lastTrace.toExactTerminalWindow
        hprefix.1 hgap hprovenance.2
      have hsecondFirst := frozenInterior_disjoint_of_window_pair_provenance
        transition.transition.firstTrace.toExactTerminalWindow
        transition.transition.lastTrace.toExactTerminalWindow
        hprefix.2 hgap hprovenance.1
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
      let assembly := appendAssembly prefixAssembly suffixAssembly
        hfirstPath hsecondPath hfirstSecondTail hsecondFirstTail
      exact .straight assembly
        (append_interiorSeparatedFromFuture prefixAssembly suffixAssembly
          hfirstPath hsecondPath hfirstSecondTail hsecondFirstTail
          hprefix hfuture (by
            change cutoff ≤ firstInterior.center.val + 2
            omega))
  | swapped suffixAssembly =>
      rw [hresult] at hfuture hprovenance
      change suffixAssembly.SeparatedFromFutureSelectedWindows
        (corridor := corridor)
        (ThirdInterior (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center.val
        at hfuture
      have hfirstFirst := frozenInterior_disjoint_of_window_pair_provenance
        transition.transition.firstTrace.toExactTerminalWindow
        transition.transition.lastTrace.toExactTerminalWindow
        hprefix.1 hgap hprovenance.1
      have hsecondSecond := frozenInterior_disjoint_of_window_pair_provenance
        transition.transition.firstTrace.toExactTerminalWindow
        transition.transition.lastTrace.toExactTerminalWindow
        hprefix.2 hgap hprovenance.2
      have hfirstSecond := frozenInterior_disjoint_of_window_pair_provenance
        transition.transition.firstTrace.toExactTerminalWindow
        transition.transition.lastTrace.toExactTerminalWindow
        hprefix.1 hgap hprovenance.2
      have hsecondFirst := frozenInterior_disjoint_of_window_pair_provenance
        transition.transition.firstTrace.toExactTerminalWindow
        transition.transition.lastTrace.toExactTerminalWindow
        hprefix.2 hgap hprovenance.1
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
      let assembly := appendAssembly prefixAssembly suffixAssembly
        hfirstPath hsecondPath hfirstSecondTail hsecondFirstTail
      exact .swapped assembly
        (append_interiorSeparatedFromFuture prefixAssembly suffixAssembly
          hfirstPath hsecondPath hfirstSecondTail hsecondFirstTail
          hprefix hfuture (by
            change cutoff ≤ firstInterior.center.val + 2
            omega))
  | straightStraightCollision =>
      exact .collision (by rw [hresult]; trivial)
  | straightSwappedCollision =>
      exact .collision (by rw [hresult]; trivial)
  | swappedStraightCollision =>
      exact .collision (by rw [hresult]; trivial)
  | swappedSwappedCollision =>
      exact .collision (by rw [hresult]; trivial)

end SupportCertifiedExactSelectedLocalRailTracedFourCellTransition

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
