import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailFrozenPrefixSeparation

/-!
# L1: attach a frozen selected-rail prefix to a remote terminal window

The rolling construction keeps an unbounded prefix behind a bounded mutable
window.  The prefix invariant says that both frozen supports avoid every
sufficiently later certified two-centre carrier.  Consequently, once the next
terminal window is beyond the stored cutoff, all four same-track and
cross-track premises of `CertifiedSelectedLocalRailTerminalWindow.prepend`
follow at once.

This file performs that attachment and proves that the resulting assembly can
be frozen at the new window's left centre.  Thus arbitrary prefix length no
longer contributes geometric cases: only construction of the bounded local
transition and the two literal end caps remain.  This is not that local
transition, an arbitrary-length rail constructor, or closure of Fable flag L1.
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

private theorem disjoint_tail_of_disjoint
    {F : Type*} {first second : List F} (h : first.Disjoint second) :
    first.Disjoint second.tail := by
  rw [List.disjoint_left] at h ⊢
  intro face hfirst hsecond
  exact h hfirst (List.mem_of_mem_tail hsecond)

/-- The future-separation predicate on either endpoint order returned after
prepending a frozen prefix. -/
def CertifiedSelectedLocalRailTerminalWindow.PrependOutcome.HasFutureSeparation
    {firstStart secondStart : SelectedFace (web := web)}
    {prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter)}
    {window : CertifiedSelectedLocalRailTerminalWindow successor left}
    (outcome : window.PrependOutcome prefixAssembly) : Prop :=
  match outcome with
  | .straight assembly | .swapped assembly =>
      assembly.SeparatedFromFutureSelectedWindows
        (corridor := corridor) leftInterior.center.val

/-- **L1 frozen-prefix attachment.** A prefix already separated from future
windows can be attached to any certified window lying beyond its cutoff.  The
four append premises are derived, not accepted as new hypotheses. -/
noncomputable def CertifiedSelectedLocalRailTerminalWindow.prependOfFrozenPrefix
    {firstStart secondStart : SelectedFace (web := web)}
    {cutoff : Nat}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter))
    (window : CertifiedSelectedLocalRailTerminalWindow successor left)
    (hprefix : prefixAssembly.SeparatedFromFutureSelectedWindows
      (corridor := corridor) cutoff)
    (hgap : cutoff + 3 < leftInterior.center.val) :
    window.PrependOutcome prefixAssembly := by
  have hfirstFirst := hprefix.1 window.firstSupport window.firstSupport_near hgap
  have hsecondSecond := hprefix.2 window.secondSupport window.secondSupport_near hgap
  have hfirstSecond := hprefix.1 window.secondSupport window.secondSupport_near hgap
  have hsecondFirst := hprefix.2 window.firstSupport window.firstSupport_near hgap
  exact window.prepend prefixAssembly
    (disjoint_tail_of_disjoint hfirstFirst)
    (disjoint_tail_of_disjoint hsecondSecond)
    (disjoint_tail_of_disjoint hfirstSecond)
    (disjoint_tail_of_disjoint hsecondFirst)

/-- After attachment, freeze the combined assembly at the new window's left
centre.  This is the induction law separating the unbounded prefix from the
still-bounded local transition. -/
theorem CertifiedSelectedLocalRailTerminalWindow.prependOfFrozenPrefix_hasFutureSeparation
    {firstStart secondStart : SelectedFace (web := web)}
    {cutoff : Nat}
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter))
    (window : CertifiedSelectedLocalRailTerminalWindow successor left)
    (hprefix : prefixAssembly.SeparatedFromFutureSelectedWindows
      (corridor := corridor) cutoff)
    (hgap : cutoff + 3 < leftInterior.center.val) :
    (window.prependOfFrozenPrefix prefixAssembly hprefix hgap).HasFutureSeparation := by
  have hcutoff : cutoff ≤ leftInterior.center.val := by omega
  have hprefix' : prefixAssembly.SeparatedFromFutureSelectedWindows
      (corridor := corridor) leftInterior.center.val :=
    ⟨SupportSeparatedFromFutureSelectedWindows.mono hprefix.1 hcutoff,
      SupportSeparatedFromFutureSelectedWindows.mono hprefix.2 hcutoff⟩
  rcases window with ⟨outcome, hprovenance⟩
  cases outcome with
  | straight terminalAssembly =>
      have hfirstFirst := hprefix.1 terminalAssembly.firstRail.support
        hprovenance.1 hgap
      have hsecondSecond := hprefix.2 terminalAssembly.secondRail.support
        hprovenance.2 hgap
      have hfirstSecond := hprefix.1 terminalAssembly.secondRail.support
        hprovenance.2 hgap
      have hsecondFirst := hprefix.2 terminalAssembly.firstRail.support
        hprovenance.1 hgap
      have hterminal : terminalAssembly.SeparatedFromFutureSelectedWindows
          (corridor := corridor) leftInterior.center.val := by
        constructor
        · intro futureInterior hfutureNext futureSupport hnear hfutureGap
          exact supports_disjoint_of_near_selected_center_pairs_of_add_three_lt
            hsource terminalAssembly.firstRail.support futureSupport
              hprovenance.1 hnear hfutureGap
        · intro futureInterior hfutureNext futureSupport hnear hfutureGap
          exact supports_disjoint_of_near_selected_center_pairs_of_add_three_lt
            hsource terminalAssembly.secondRail.support futureSupport
              hprovenance.2 hnear hfutureGap
      simpa [CertifiedSelectedLocalRailTerminalWindow.prependOfFrozenPrefix,
        CertifiedSelectedLocalRailTerminalWindow.prepend,
        CertifiedSelectedLocalRailTerminalWindow.PrependOutcome.HasFutureSeparation]
        using appendAssembly_separatedFromFutureSelectedWindows
          prefixAssembly terminalAssembly
          (disjoint_tail_of_disjoint hfirstFirst)
          (disjoint_tail_of_disjoint hsecondSecond)
          (disjoint_tail_of_disjoint hfirstSecond)
          (disjoint_tail_of_disjoint hsecondFirst)
          hprefix' hterminal
  | swapped terminalAssembly =>
      have hfirstFirst := hprefix.1 terminalAssembly.firstRail.support
        hprovenance.1 hgap
      have hsecondSecond := hprefix.2 terminalAssembly.secondRail.support
        hprovenance.2 hgap
      have hfirstSecond := hprefix.1 terminalAssembly.secondRail.support
        hprovenance.2 hgap
      have hsecondFirst := hprefix.2 terminalAssembly.firstRail.support
        hprovenance.1 hgap
      have hterminal : terminalAssembly.SeparatedFromFutureSelectedWindows
          (corridor := corridor) leftInterior.center.val := by
        constructor
        · intro futureInterior hfutureNext futureSupport hnear hfutureGap
          exact supports_disjoint_of_near_selected_center_pairs_of_add_three_lt
            hsource terminalAssembly.firstRail.support futureSupport
              hprovenance.1 hnear hfutureGap
        · intro futureInterior hfutureNext futureSupport hnear hfutureGap
          exact supports_disjoint_of_near_selected_center_pairs_of_add_three_lt
            hsource terminalAssembly.secondRail.support futureSupport
              hprovenance.2 hnear hfutureGap
      simpa [CertifiedSelectedLocalRailTerminalWindow.prependOfFrozenPrefix,
        CertifiedSelectedLocalRailTerminalWindow.prepend,
        CertifiedSelectedLocalRailTerminalWindow.PrependOutcome.HasFutureSeparation]
        using appendAssembly_separatedFromFutureSelectedWindows
          prefixAssembly terminalAssembly
          (disjoint_tail_of_disjoint hfirstFirst)
          (disjoint_tail_of_disjoint hsecondSecond)
          (disjoint_tail_of_disjoint hfirstSecond)
          (disjoint_tail_of_disjoint hsecondFirst)
          hprefix' hterminal

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
