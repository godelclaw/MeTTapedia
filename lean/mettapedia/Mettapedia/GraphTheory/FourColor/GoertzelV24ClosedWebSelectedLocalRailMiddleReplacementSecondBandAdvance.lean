import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSecondBandFutureSeparation
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailTracedFourCellSupport

/-!
# L1: advance the second-band endpoint through a canonical future window

The fourth-cell far-end residue must be rolled far enough that it is no longer
the requested output endpoint.  The canonical four-cell classifier may erase
that face while repairing its rails.  That is already a successful clearance,
not a loss of evidence.  If the face survives, remote source separation proves
that it is not either output endpoint.

This file records that exact fail-closed alternative for the actual canonical
future transition: a collision remains an exact collision-bearing outcome;
otherwise the old face is absent from both returned rails, or occurs on exactly
one returned rail strictly before its remote finish.  No prefix-preservation
hypothesis is introduced.

The theorem is an endpoint-advance receipt.  It does not eliminate a collision
in the new four-cell window, build the collision-removing centre bridge for a
surviving occurrence, attach end caps, or close Fable flag L1.
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
    {firstInterior : CorridorInterior blockLength}
    {hfirstNext : firstInterior.center.val + 2 < blockLength}
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {hlastNext :
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center.val +
          2 < blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
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

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev FourthInterior :=
  nextCorridorInterior
    (nextCorridorInterior
      (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
    hlastNext

variable
    {hfourthNext :
      (FourthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
        (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)).center.val + 2 <
          blockLength}
    {hfifthNext :
      (nextCorridorInterior
        (FourthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
          (hbridgeNext := hbridgeNext) (hlastNext := hlastNext))
        hfourthNext).center.val + 2 < blockLength}
    {hsixthNext :
      (nextCorridorInterior
        (nextCorridorInterior
          (FourthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
            (hbridgeNext := hbridgeNext) (hlastNext := hlastNext))
          hfourthNext)
        hfifthNext).center.val + 2 < blockLength}
    {fifthPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (FourthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
          (hbridgeNext := hbridgeNext) (hlastNext := hlastNext))
        hfourthNext)}
    {sixthPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior
          (FourthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
            (hbridgeNext := hbridgeNext) (hlastNext := hlastNext))
          hfourthNext)
        hfifthNext)}
    {seventhPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior
            (FourthInterior (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext))
            hfourthNext)
          hfifthNext)
        hsixthNext)}
    {fourthSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfourthNext
      fourthPlacement fifthPlacement}
    {fifthSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfifthNext
      fifthPlacement sixthPlacement}
    {sixthSuccessor : SeparatedSelectedSourceLocalRailSuccessor hsixthNext
      sixthPlacement seventhPlacement}

private abbrev FutureFirstLeft :=
  lastSuccessor.rightRailsAsNextLeft fourthSuccessor

/-- Successful future outcomes either clear the old fourth-cell endpoint, or
retain it on exactly one rail strictly before that rail's remote finish.
Collision constructors remain explicit in the outcome itself and impose no
false success claim. -/
def ExactSelectedLocalRailFourCellRetainedOutcome.ResolvesFourthFarEndpointAtFinish
    {firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      fourthSuccessor
      (FutureFirstLeft (lastSuccessor := lastSuccessor)
        (fourthSuccessor := fourthSuccessor))}
    {lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow sixthSuccessor
      (fifthSuccessor.rightRailsAsNextLeft sixthSuccessor)}
    (outcome : ExactSelectedLocalRailFourCellRetainedOutcome
      firstWindow lastWindow)
    (face : SelectedFace (web := web)) : Prop :=
  match outcome with
  | .straight assembly =>
      (face ∉ assembly.firstRail.support ∧
          face ∉ assembly.secondRail.support) ∨
      (face ∈ assembly.firstRail.support ∧
          face ∉ assembly.secondRail.support ∧
          face ≠ selectedPlacementSideFace seventhPlacement
            sixthSuccessor.rightOutgoingBefore) ∨
      (face ∉ assembly.firstRail.support ∧
          face ∈ assembly.secondRail.support ∧
          face ≠ selectedPlacementSideFace seventhPlacement
            sixthSuccessor.rightOutgoingAfter)
  | .swapped assembly =>
      (face ∉ assembly.firstRail.support ∧
          face ∉ assembly.secondRail.support) ∨
      (face ∈ assembly.firstRail.support ∧
          face ∉ assembly.secondRail.support ∧
          face ≠ selectedPlacementSideFace seventhPlacement
            sixthSuccessor.rightOutgoingAfter) ∨
      (face ∉ assembly.firstRail.support ∧
          face ∈ assembly.secondRail.support ∧
          face ≠ selectedPlacementSideFace seventhPlacement
            sixthSuccessor.rightOutgoingBefore)
  | .straightStraightCollision _ _ _ _ _
  | .straightSwappedCollision _ _ _ _ _
  | .swappedStraightCollision _ _ _ _ _
  | .swappedSwappedCollision _ _ _ _ _ => True

/-- **L1 canonical second-band advance.** The actual classifier on the next
four-cell window either retains its exact collision outcome, clears the old
far endpoint, or makes that face nonterminal on exactly one successful rail.
Loop erasure is therefore harmless for this endpoint argument: deletion is
success, while survival supplies the internal occurrence needed by the next
repair. -/
theorem SecondFourthFarEndpoint.canonicalFutureTransition_resolvesAtFinish
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {face : SelectedFace (web := web)}
    (endpoint : SecondFourthFarEndpoint
      (fourthPlacement := fourthPlacement) (lastSuccessor := lastSuccessor) face) :
    let transition :=
      SupportCertifiedExactSelectedLocalRailTracedFourCellTransition.ofClassifiers
        (firstSuccessor := fourthSuccessor) (bridge := fifthSuccessor)
        (lastSuccessor := sixthSuccessor)
        (firstLeft := FutureFirstLeft (lastSuccessor := lastSuccessor)
          (fourthSuccessor := fourthSuccessor)) hsource
    transition.transition.outcome.ResolvesFourthFarEndpointAtFinish face := by
  let transition :=
    SupportCertifiedExactSelectedLocalRailTracedFourCellTransition.ofClassifiers
      (firstSuccessor := fourthSuccessor) (bridge := fifthSuccessor)
      (lastSuccessor := sixthSuccessor)
      (firstLeft := FutureFirstLeft (lastSuccessor := lastSuccessor)
        (fourthSuccessor := fourthSuccessor)) hsource
  change transition.transition.outcome.ResolvesFourthFarEndpointAtFinish face
  have hremote :
      (FourthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
        (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)).center.val + 2 <
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior
            (FourthInterior (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext))
            hfourthNext)
          hfifthNext)
        hsixthNext).center.val := by
    change firstInterior.center.val + 3 + 2 < firstInterior.center.val + 6
    omega
  have hfuture := endpoint.not_mem_futureRailSupports hsource
    sixthSuccessor.rightRails.paths hremote
  cases hresult : transition.transition.outcome with
  | straight assembly =>
      change
        (face ∉ assembly.firstRail.support ∧ face ∉ assembly.secondRail.support) ∨
        (face ∈ assembly.firstRail.support ∧ face ∉ assembly.secondRail.support ∧
          face ≠ selectedPlacementSideFace seventhPlacement
            sixthSuccessor.rightOutgoingBefore) ∨
        (face ∉ assembly.firstRail.support ∧ face ∈ assembly.secondRail.support ∧
          face ≠ selectedPlacementSideFace seventhPlacement
            sixthSuccessor.rightOutgoingAfter)
      have hfirstFinish : face ≠ selectedPlacementSideFace seventhPlacement
          sixthSuccessor.rightOutgoingBefore := by
        intro heq
        exact hfuture.1 (heq ▸ sixthSuccessor.rightRails.paths.firstRail.end_mem_support)
      have hsecondFinish : face ≠ selectedPlacementSideFace seventhPlacement
          sixthSuccessor.rightOutgoingAfter := by
        intro heq
        exact hfuture.2 (heq ▸ sixthSuccessor.rightRails.paths.secondRail.end_mem_support)
      by_cases hfirst : face ∈ assembly.firstRail.support
      · have hsecond : face ∉ assembly.secondRail.support := by
          intro hsecond
          exact (List.disjoint_left.mp
            assembly.firstRail_support_disjoint_secondRail hfirst) hsecond
        exact .inr (.inl ⟨hfirst, hsecond, hfirstFinish⟩)
      · by_cases hsecond : face ∈ assembly.secondRail.support
        · exact .inr (.inr ⟨hfirst, hsecond, hsecondFinish⟩)
        · exact .inl ⟨hfirst, hsecond⟩
  | swapped assembly =>
      change
        (face ∉ assembly.firstRail.support ∧ face ∉ assembly.secondRail.support) ∨
        (face ∈ assembly.firstRail.support ∧ face ∉ assembly.secondRail.support ∧
          face ≠ selectedPlacementSideFace seventhPlacement
            sixthSuccessor.rightOutgoingAfter) ∨
        (face ∉ assembly.firstRail.support ∧ face ∈ assembly.secondRail.support ∧
          face ≠ selectedPlacementSideFace seventhPlacement
            sixthSuccessor.rightOutgoingBefore)
      have hfirstFinish : face ≠ selectedPlacementSideFace seventhPlacement
          sixthSuccessor.rightOutgoingAfter := by
        intro heq
        exact hfuture.2 (heq ▸ sixthSuccessor.rightRails.paths.secondRail.end_mem_support)
      have hsecondFinish : face ≠ selectedPlacementSideFace seventhPlacement
          sixthSuccessor.rightOutgoingBefore := by
        intro heq
        exact hfuture.1 (heq ▸ sixthSuccessor.rightRails.paths.firstRail.end_mem_support)
      by_cases hfirst : face ∈ assembly.firstRail.support
      · have hsecond : face ∉ assembly.secondRail.support := by
          intro hsecond
          exact (List.disjoint_left.mp
            assembly.firstRail_support_disjoint_secondRail hfirst) hsecond
        exact .inr (.inl ⟨hfirst, hsecond, hfirstFinish⟩)
      · by_cases hsecond : face ∈ assembly.secondRail.support
        · exact .inr (.inr ⟨hfirst, hsecond, hsecondFinish⟩)
        · exact .inl ⟨hfirst, hsecond⟩
  | straightStraightCollision => trivial
  | straightSwappedCollision => trivial
  | swappedStraightCollision => trivial
  | swappedSwappedCollision => trivial

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
