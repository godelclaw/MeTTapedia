import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailFrozenPrefixInterfaceObstruction

/-!
# L1: prepend a rail prefix with only its interior support frozen

The interface obstruction shows that a complete prefix cannot be disjoint
from a window attached at its final faces.  The correct invariant removes
exactly those two final interface occurrences.  The remaining `dropLast`
supports are genuinely frozen; the named final faces belong to the bounded
live interface.

This module proves the corresponding seed-and-step laws.  Every certified
terminal window supplies the interior-frozen invariant.  Given an older
assembly carrying it, path simplicity permits the two shared endpoints while
the invariant discharges all other same-track and cross-track contacts.  The
resulting ordered or exchanged assembly is constructed and carries the same
interior invariant at the new cutoff.

This is the interface-aware algebra required by the rolling construction.  It
does not construct the bounded four-cell transition which supplies successive
compatible windows, attach either end cap, or close Fable flag L1.
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

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- Freeze only the rail interiors.  The two omitted final occurrences are
the live splice interface owned by the bounded terminal window. -/
def InteriorSeparatedFromFutureSelectedWindows
    {firstStart secondStart firstFinish secondFinish : SelectedFace (web := web)}
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart firstFinish secondFinish)
    (cutoff : Nat) : Prop :=
  SupportSeparatedFromFutureSelectedWindows (corridor := corridor) cutoff
      assembly.firstRail.support.dropLast ∧
    SupportSeparatedFromFutureSelectedWindows (corridor := corridor) cutoff
      assembly.secondRail.support.dropLast

/-- Removing the final occurrence preserves any full-support future
separation certificate. -/
theorem supportSeparatedFromFutureSelectedWindows_dropLast
    {cutoff : Nat} {support : List (SelectedFace (web := web))}
    (hfrozen : SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor) cutoff support) :
    SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor) cutoff support.dropLast := by
  intro futureInterior hfutureNext futureSupport hnear hgap
  have hdisjoint := hfrozen futureSupport hnear hgap
  rw [List.disjoint_left] at hdisjoint ⊢
  intro face hdrop hfuture
  exact hdisjoint (List.mem_of_mem_dropLast hdrop) hfuture

/-- Advancing the cutoff preserves an interior-frozen assembly. -/
theorem InteriorSeparatedFromFutureSelectedWindows.mono
    {firstStart secondStart firstFinish secondFinish : SelectedFace (web := web)}
    {assembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart firstFinish secondFinish}
    {oldCutoff newCutoff : Nat}
    (hfrozen : InteriorSeparatedFromFutureSelectedWindows
      (corridor := corridor) assembly oldCutoff)
    (hle : oldCutoff ≤ newCutoff) :
    InteriorSeparatedFromFutureSelectedWindows
      (corridor := corridor) assembly newCutoff :=
  ⟨SupportSeparatedFromFutureSelectedWindows.mono hfrozen.1 hle,
    SupportSeparatedFromFutureSelectedWindows.mono hfrozen.2 hle⟩

theorem walk_support_disjoint_tail_of_dropLast_disjoint_of_end_not_mem
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

theorem walk_support_disjoint_tail_of_dropLast_disjoint
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

theorem dropLast_append_of_right_ne_nil
    {A : Type*} (left right : List A) (hright : right ≠ []) :
    (left ++ right).dropLast = left ++ right.dropLast := by
  induction left with
  | nil => simp
  | cons head tail ih =>
      have htail : tail ++ right ≠ [] :=
        List.append_ne_nil_of_right_ne_nil tail hright
      rw [List.cons_append, List.dropLast_cons_of_ne_nil htail, ih]
      rfl

theorem appendAssembly_interiorSeparatedFromFuture
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
    (hsuffix : InteriorSeparatedFromFutureSelectedWindows
      (corridor := corridor) suffixAssembly newCutoff)
    (hle : oldCutoff ≤ newCutoff) :
    InteriorSeparatedFromFutureSelectedWindows (corridor := corridor)
      (appendAssembly prefixAssembly suffixAssembly hfirstPath hsecondPath
        hfirstSecond hsecondFirst) newCutoff := by
  constructor
  · change SupportSeparatedFromFutureSelectedWindows (corridor := corridor) newCutoff
      (prefixAssembly.firstRail.append suffixAssembly.firstRail).support.dropLast
    rw [SimpleGraph.Walk.support_append_eq_support_dropLast_append,
      dropLast_append_of_right_ne_nil _ _ suffixAssembly.firstRail.support_ne_nil]
    exact supportSeparatedFromFutureSelectedWindows_append
      (SupportSeparatedFromFutureSelectedWindows.mono hprefix.1 hle) hsuffix.1
  · change SupportSeparatedFromFutureSelectedWindows (corridor := corridor) newCutoff
      (prefixAssembly.secondRail.append suffixAssembly.secondRail).support.dropLast
    rw [SimpleGraph.Walk.support_append_eq_support_dropLast_append,
      dropLast_append_of_right_ne_nil _ _ suffixAssembly.secondRail.support_ne_nil]
    exact supportSeparatedFromFutureSelectedWindows_append
      (SupportSeparatedFromFutureSelectedWindows.mono hprefix.2 hle) hsuffix.2

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

/-- Interior-future-separation predicate on either endpoint order of a
certified terminal window. -/
def CertifiedSelectedLocalRailTerminalWindow.HasInteriorFutureSeparation
    (window : CertifiedSelectedLocalRailTerminalWindow successor left) : Prop :=
  match window.outcome with
  | .straight assembly | .swapped assembly =>
      InteriorSeparatedFromFutureSelectedWindows
        (corridor := corridor) assembly leftInterior.center.val

/-- Every certified terminal window is a constructed seed for the corrected
interior-frozen invariant. -/
theorem CertifiedSelectedLocalRailTerminalWindow.hasInteriorFutureSeparation
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (window : CertifiedSelectedLocalRailTerminalWindow successor left) :
    window.HasInteriorFutureSeparation := by
  have hfirst : SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor) leftInterior.center.val window.firstSupport :=
    CertifiedSelectedLocalRailTerminalWindow.firstSupport_separatedFromFuture
      hsource window
  have hsecond : SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor) leftInterior.center.val window.secondSupport :=
    CertifiedSelectedLocalRailTerminalWindow.secondSupport_separatedFromFuture
      hsource window
  rcases window with ⟨outcome, hprovenance⟩
  cases outcome with
  | straight assembly =>
      exact ⟨supportSeparatedFromFutureSelectedWindows_dropLast hfirst,
        supportSeparatedFromFutureSelectedWindows_dropLast hsecond⟩
  | swapped assembly =>
      exact ⟨supportSeparatedFromFutureSelectedWindows_dropLast hfirst,
        supportSeparatedFromFutureSelectedWindows_dropLast hsecond⟩

/-- The two possible endpoint orders after an interface-aware frozen prefix
is attached to a certified terminal window. -/
inductive CertifiedSelectedLocalRailTerminalWindow.InteriorFrozenPrependOutcome
    {firstStart secondStart : SelectedFace (web := web)}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter))
    (window : CertifiedSelectedLocalRailTerminalWindow successor left) : Type (u + 1)
  | straight
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        firstStart secondStart
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter))
      (interiorSeparated : InteriorSeparatedFromFutureSelectedWindows
        (corridor := corridor) assembly leftInterior.center.val)
  | swapped
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        firstStart secondStart
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore))
      (interiorSeparated : InteriorSeparatedFromFutureSelectedWindows
        (corridor := corridor) assembly leftInterior.center.val)

/-- **L1 interface-aware prepend.** Full disjointness is required only of the
frozen interiors.  The two shared splice faces are discharged by path
simplicity, so no impossible full-support premise is introduced. -/
noncomputable def CertifiedSelectedLocalRailTerminalWindow.prependInteriorFrozen
    {firstStart secondStart : SelectedFace (web := web)}
    {cutoff : Nat}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter))
    (window : CertifiedSelectedLocalRailTerminalWindow successor left)
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (hprefix : InteriorSeparatedFromFutureSelectedWindows
      (corridor := corridor) prefixAssembly cutoff)
    (hgap : cutoff + 3 < leftInterior.center.val) :
    window.InteriorFrozenPrependOutcome prefixAssembly := by
  have hwindowFrozen := window.hasInteriorFutureSeparation hsource
  rcases window with ⟨outcome, hprovenance⟩
  cases outcome with
  | straight terminalAssembly =>
      change InteriorSeparatedFromFutureSelectedWindows (corridor := corridor)
        terminalAssembly leftInterior.center.val at hwindowFrozen
      have hfirstFirst := hprefix.1 terminalAssembly.firstRail.support
        hprovenance.1 hgap
      have hsecondSecond := hprefix.2 terminalAssembly.secondRail.support
        hprovenance.2 hgap
      have hfirstSecond := hprefix.1 terminalAssembly.secondRail.support
        hprovenance.2 hgap
      have hsecondFirst := hprefix.2 terminalAssembly.firstRail.support
        hprovenance.1 hgap
      have hfirstEndNotSecondTail :
          selectedPlacementSideFace leftPlacement leftIncomingBefore ∉
            terminalAssembly.secondRail.support.tail := by
        intro hmem
        exact (List.disjoint_left.mp
          terminalAssembly.firstRail_support_disjoint_secondRail
          terminalAssembly.firstRail.start_mem_support)
          (List.mem_of_mem_tail hmem)
      have hsecondEndNotFirstTail :
          selectedPlacementSideFace leftPlacement leftIncomingAfter ∉
            terminalAssembly.firstRail.support.tail := by
        intro hmem
        exact (List.disjoint_left.mp
          terminalAssembly.firstRail_support_disjoint_secondRail
          (List.mem_of_mem_tail hmem))
          terminalAssembly.secondRail.start_mem_support
      have hfirstPath := walk_support_disjoint_tail_of_dropLast_disjoint
          prefixAssembly.firstRail terminalAssembly.firstRail
          terminalAssembly.firstRail_isPath hfirstFirst
      have hsecondPath := walk_support_disjoint_tail_of_dropLast_disjoint
          prefixAssembly.secondRail terminalAssembly.secondRail
          terminalAssembly.secondRail_isPath hsecondSecond
      have hfirstSecondTail :=
        walk_support_disjoint_tail_of_dropLast_disjoint_of_end_not_mem
          prefixAssembly.firstRail terminalAssembly.secondRail
          hfirstSecond hfirstEndNotSecondTail
      have hsecondFirstTail :=
        walk_support_disjoint_tail_of_dropLast_disjoint_of_end_not_mem
          prefixAssembly.secondRail terminalAssembly.firstRail
          hsecondFirst hsecondEndNotFirstTail
      let appended := appendAssembly prefixAssembly terminalAssembly
        hfirstPath hsecondPath hfirstSecondTail hsecondFirstTail
      exact .straight appended
        (appendAssembly_interiorSeparatedFromFuture prefixAssembly terminalAssembly
          hfirstPath hsecondPath hfirstSecondTail hsecondFirstTail hprefix hwindowFrozen
          (by omega))
  | swapped terminalAssembly =>
      change InteriorSeparatedFromFutureSelectedWindows (corridor := corridor)
        terminalAssembly leftInterior.center.val at hwindowFrozen
      have hfirstFirst := hprefix.1 terminalAssembly.firstRail.support
        hprovenance.1 hgap
      have hsecondSecond := hprefix.2 terminalAssembly.secondRail.support
        hprovenance.2 hgap
      have hfirstSecond := hprefix.1 terminalAssembly.secondRail.support
        hprovenance.2 hgap
      have hsecondFirst := hprefix.2 terminalAssembly.firstRail.support
        hprovenance.1 hgap
      have hfirstEndNotSecondTail :
          selectedPlacementSideFace leftPlacement leftIncomingBefore ∉
            terminalAssembly.secondRail.support.tail := by
        intro hmem
        exact (List.disjoint_left.mp
          terminalAssembly.firstRail_support_disjoint_secondRail
          terminalAssembly.firstRail.start_mem_support)
          (List.mem_of_mem_tail hmem)
      have hsecondEndNotFirstTail :
          selectedPlacementSideFace leftPlacement leftIncomingAfter ∉
            terminalAssembly.firstRail.support.tail := by
        intro hmem
        exact (List.disjoint_left.mp
          terminalAssembly.firstRail_support_disjoint_secondRail
          (List.mem_of_mem_tail hmem))
          terminalAssembly.secondRail.start_mem_support
      have hfirstPath := walk_support_disjoint_tail_of_dropLast_disjoint
          prefixAssembly.firstRail terminalAssembly.firstRail
          terminalAssembly.firstRail_isPath hfirstFirst
      have hsecondPath := walk_support_disjoint_tail_of_dropLast_disjoint
          prefixAssembly.secondRail terminalAssembly.secondRail
          terminalAssembly.secondRail_isPath hsecondSecond
      have hfirstSecondTail :=
        walk_support_disjoint_tail_of_dropLast_disjoint_of_end_not_mem
          prefixAssembly.firstRail terminalAssembly.secondRail
          hfirstSecond hfirstEndNotSecondTail
      have hsecondFirstTail :=
        walk_support_disjoint_tail_of_dropLast_disjoint_of_end_not_mem
          prefixAssembly.secondRail terminalAssembly.firstRail
          hsecondFirst hsecondEndNotFirstTail
      let appended := appendAssembly prefixAssembly terminalAssembly
        hfirstPath hsecondPath hfirstSecondTail hsecondFirstTail
      exact .swapped appended
        (appendAssembly_interiorSeparatedFromFuture prefixAssembly terminalAssembly
          hfirstPath hsecondPath hfirstSecondTail hsecondFirstTail hprefix hwindowFrozen
          (by omega))

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
