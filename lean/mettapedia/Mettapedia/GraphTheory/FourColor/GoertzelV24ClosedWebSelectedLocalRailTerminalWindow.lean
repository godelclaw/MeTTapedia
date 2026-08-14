import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailWindowSeparation

/-!
# L1: certified terminal window for selected corridor rails

The complete adjacent append returns an actual straight-or-swapped pair of
simple disjoint rails, and the window-separation layer proves that both
supports stay in the closed dual neighbourhood of the two literal Cell-3
centres.  This module packages those two facts without erasing the endpoint
permutation.

The resulting carrier is the seed for the length-direction induction.  Its
supports are internally disjoint and are disjoint from every sufficiently
remote future two-centre window.  This is not yet a transition-closed state:
the next neighbouring repair may replace part of the current terminal window,
so a later theorem must retain enough finite branch data to advance the
window before freezing its remote prefix.  No arbitrary-length rail, annular
end cap, or Fable flag L1 closure is claimed here.
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

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- A complete adjacent append together with the literal two-centre support
certificate proved for the exact outcome it returns. -/
structure CertifiedSelectedLocalRailTerminalWindow
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) where
  outcome : SelectedLocalRailAppendCompleteOutcome successor left
  hasWindowProvenance : outcome.HasWindowProvenance (corridor := corridor)

/-- The canonical certified window supplied by the unconditional adjacent
append theorem. -/
noncomputable def CertifiedSelectedLocalRailTerminalWindow.ofComplete
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter) :
    CertifiedSelectedLocalRailTerminalWindow successor left :=
  ⟨appendLocalSuccessorComplete successor left,
    appendLocalSuccessorComplete_hasWindowProvenance⟩

/-- The first facial support, independent of the endpoint permutation. -/
def CertifiedSelectedLocalRailTerminalWindow.firstSupport
    (window : CertifiedSelectedLocalRailTerminalWindow successor left) :
    List (SelectedFace (web := web)) :=
  match window.outcome with
  | .straight assembly => assembly.firstRail.support
  | .swapped assembly => assembly.firstRail.support

/-- The second facial support, independent of the endpoint permutation. -/
def CertifiedSelectedLocalRailTerminalWindow.secondSupport
    (window : CertifiedSelectedLocalRailTerminalWindow successor left) :
    List (SelectedFace (web := web)) :=
  match window.outcome with
  | .straight assembly => assembly.secondRail.support
  | .swapped assembly => assembly.secondRail.support

/-- The first support carries the certified adjacent two-centre provenance. -/
theorem CertifiedSelectedLocalRailTerminalWindow.firstSupport_near
    (window : CertifiedSelectedLocalRailTerminalWindow successor left) :
    SupportNearSelectedCenterPair (corridor := corridor)
      leftInterior.center (nextCorridorInterior leftInterior hnext).center
      window.firstSupport := by
  rcases window with ⟨outcome, hprovenance⟩
  cases outcome with
  | straight assembly => exact hprovenance.1
  | swapped assembly => exact hprovenance.1

/-- The second support carries the same provenance. -/
theorem CertifiedSelectedLocalRailTerminalWindow.secondSupport_near
    (window : CertifiedSelectedLocalRailTerminalWindow successor left) :
    SupportNearSelectedCenterPair (corridor := corridor)
      leftInterior.center (nextCorridorInterior leftInterior hnext).center
      window.secondSupport := by
  rcases window with ⟨outcome, hprovenance⟩
  cases outcome with
  | straight assembly => exact hprovenance.2
  | swapped assembly => exact hprovenance.2

/-- Mutual separation survives packaging and does not depend on whether the
outgoing labels are straight or exchanged. -/
theorem CertifiedSelectedLocalRailTerminalWindow.firstSupport_disjoint_secondSupport
    (window : CertifiedSelectedLocalRailTerminalWindow successor left) :
    window.firstSupport.Disjoint window.secondSupport := by
  rcases window with ⟨outcome, _⟩
  cases outcome with
  | straight assembly => exact assembly.firstRail_support_disjoint_secondRail
  | swapped assembly => exact assembly.firstRail_support_disjoint_secondRail

/-- The first terminal support is disjoint from every support carried by a
sufficiently remote future adjacent window. -/
theorem CertifiedSelectedLocalRailTerminalWindow.firstSupport_disjoint_of_remote
    (window : CertifiedSelectedLocalRailTerminalWindow successor left)
    {futureInterior : CorridorInterior blockLength}
    {hfutureNext : futureInterior.center.val + 2 < blockLength}
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (futureSupport : List (SelectedFace (web := web)))
    (hfuture : SupportNearSelectedCenterPair (corridor := corridor)
      futureInterior.center
      (nextCorridorInterior futureInterior hfutureNext).center futureSupport)
    (hseparated : leftInterior.center.val + 3 < futureInterior.center.val) :
    window.firstSupport.Disjoint futureSupport :=
  supports_disjoint_of_near_selected_center_pairs_of_add_three_lt
    hsource window.firstSupport futureSupport window.firstSupport_near
      hfuture hseparated

/-- The symmetric remote-separation theorem for the second terminal support. -/
theorem CertifiedSelectedLocalRailTerminalWindow.secondSupport_disjoint_of_remote
    (window : CertifiedSelectedLocalRailTerminalWindow successor left)
    {futureInterior : CorridorInterior blockLength}
    {hfutureNext : futureInterior.center.val + 2 < blockLength}
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (futureSupport : List (SelectedFace (web := web)))
    (hfuture : SupportNearSelectedCenterPair (corridor := corridor)
      futureInterior.center
      (nextCorridorInterior futureInterior hfutureNext).center futureSupport)
    (hseparated : leftInterior.center.val + 3 < futureInterior.center.val) :
    window.secondSupport.Disjoint futureSupport :=
  supports_disjoint_of_near_selected_center_pairs_of_add_three_lt
    hsource window.secondSupport futureSupport window.secondSupport_near
      hfuture hseparated

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
