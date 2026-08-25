import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailTracedFourCellSupport
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailFrozenPrefixSeparation

/-!
# L1: future separation of a canonical four-cell rail output

The canonical four-cell classifier may loop-erase its two input terminal
windows.  Support provenance proves that this operation removes faces but
does not invent them.  The remote-window theorem can therefore be transported
from the four literal input rails to either successful output rail.

The cutoff is the left centre of the last two-cell terminal window.  This is
the full-support receipt needed before its interior can be frozen and the
bounded live suffix advanced.  Collision alternatives remain explicit; this
module does not eliminate them, perform the rolling induction, attach either
end cap, or close Fable flag L1.
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

private abbrev LastLeft :=
  bridge.rightRailsAsNextLeft lastSuccessor

/-- Successful four-cell outcomes are disjoint from every sufficiently remote
future selected window.  Collision alternatives keep their witness and make
no success claim. -/
def ExactSelectedLocalRailFourCellRetainedOutcome.HasFutureSeparation
    {firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft}
    {lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))}
    (outcome : ExactSelectedLocalRailFourCellRetainedOutcome
      firstWindow lastWindow) : Prop :=
  match outcome with
  | .straight assembly | .swapped assembly =>
      assembly.SeparatedFromFutureSelectedWindows (corridor := corridor)
        (ThirdInterior (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center.val
  | .straightStraightCollision _ _ _ _ _
  | .straightSwappedCollision _ _ _ _ _
  | .swappedStraightCollision _ _ _ _ _
  | .swappedSwappedCollision _ _ _ _ _ => True

private theorem supportSeparatedFromFuture_of_containedInExactTerminalWindowPair
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)))
    {support : List (SelectedFace (web := web))}
    (hcontained : SupportContainedInExactTerminalWindowPair
      firstWindow lastWindow support) :
    SupportSeparatedFromFutureSelectedWindows (corridor := corridor)
      (ThirdInterior (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center.val
      support := by
  have hfirstFirst : SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor) firstInterior.center.val
      firstWindow.toCertified.firstSupport :=
    CertifiedSelectedLocalRailTerminalWindow.firstSupport_separatedFromFuture
      (successor := firstSuccessor) (left := firstLeft)
      hsource firstWindow.toCertified
  have hfirstSecond : SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor) firstInterior.center.val
      firstWindow.toCertified.secondSupport :=
    CertifiedSelectedLocalRailTerminalWindow.secondSupport_separatedFromFuture
      (successor := firstSuccessor) (left := firstLeft)
      hsource firstWindow.toCertified
  have hfirstLe : firstInterior.center.val ≤
      (ThirdInterior (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center.val := by
    change firstInterior.center.val ≤ firstInterior.center.val + 2
    omega
  have hfirstFirst' : SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor)
      (ThirdInterior (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center.val
      firstWindow.toCertified.firstSupport :=
    SupportSeparatedFromFutureSelectedWindows.mono hfirstFirst hfirstLe
  have hfirstSecond' : SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor)
      (ThirdInterior (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center.val
      firstWindow.toCertified.secondSupport :=
    SupportSeparatedFromFutureSelectedWindows.mono hfirstSecond hfirstLe
  have hlastFirst : SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor)
      (ThirdInterior (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center.val
      lastWindow.toCertified.firstSupport :=
    CertifiedSelectedLocalRailTerminalWindow.firstSupport_separatedFromFuture
      (successor := lastSuccessor)
      (left := LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))
      hsource lastWindow.toCertified
  have hlastSecond : SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor)
      (ThirdInterior (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center.val
      lastWindow.toCertified.secondSupport :=
    CertifiedSelectedLocalRailTerminalWindow.secondSupport_separatedFromFuture
      (successor := lastSuccessor)
      (left := LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))
      hsource lastWindow.toCertified
  intro futureInterior hfutureNext futureSupport hnear hgap
  rw [List.disjoint_left]
  intro face hface hfutureFace
  rcases hcontained face hface with
    hfirstFirstFace | hfirstSecondFace | hlastFirstFace | hlastSecondFace
  · exact (List.disjoint_left.mp
      (hfirstFirst' futureSupport hnear hgap) hfirstFirstFace) hfutureFace
  · exact (List.disjoint_left.mp
      (hfirstSecond' futureSupport hnear hgap) hfirstSecondFace) hfutureFace
  · exact (List.disjoint_left.mp
      (hlastFirst futureSupport hnear hgap) hlastFirstFace) hfutureFace
  · exact (List.disjoint_left.mp
      (hlastSecond futureSupport hnear hgap) hlastSecondFace) hfutureFace

/-- Support provenance transports the future-window invariant through every
successful endpoint-parity branch of the exact four-cell result. -/
theorem ExactSelectedLocalRailFourCellRetainedOutcome.hasFutureSeparation_of_provenance
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft}
    {lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))}
    (outcome : ExactSelectedLocalRailFourCellRetainedOutcome
      firstWindow lastWindow)
    (hprovenance : outcome.HasWindowSupportProvenance) :
    outcome.HasFutureSeparation := by
  cases outcome with
  | straight assembly =>
      exact ⟨
        supportSeparatedFromFuture_of_containedInExactTerminalWindowPair
          hsource firstWindow lastWindow hprovenance.1,
        supportSeparatedFromFuture_of_containedInExactTerminalWindowPair
          hsource firstWindow lastWindow hprovenance.2⟩
  | swapped assembly =>
      exact ⟨
        supportSeparatedFromFuture_of_containedInExactTerminalWindowPair
          hsource firstWindow lastWindow hprovenance.1,
        supportSeparatedFromFuture_of_containedInExactTerminalWindowPair
          hsource firstWindow lastWindow hprovenance.2⟩
  | straightStraightCollision => trivial
  | straightSwappedCollision => trivial
  | swappedStraightCollision => trivial
  | swappedSwappedCollision => trivial

/-- The canonical support-certified transition carries future separation on
every successful output. -/
theorem SupportCertifiedExactSelectedLocalRailTracedFourCellTransition.hasFutureSeparation
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (transition : SupportCertifiedExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)) :
    transition.transition.outcome.HasFutureSeparation :=
  transition.transition.outcome.hasFutureSeparation_of_provenance
    hsource transition.hasWindowSupportProvenance

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
