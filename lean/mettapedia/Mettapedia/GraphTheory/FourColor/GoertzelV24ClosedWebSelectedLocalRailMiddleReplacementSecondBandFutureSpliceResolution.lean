import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSecondBandFutureCenterBridge

/-!
# L1: consume a surviving advanced endpoint by a literal source splice

The canonical future four-cell transition can erase the old fourth-cell
endpoint, retain it internally on one successful rail, or return a new exact
collision outcome.  In the surviving case, the retained old-rail origin and
the future terminal-window provenance now feed the literal center bridge and
generic cross-splice.

This module packages that exhaustive result.  A successful surviving branch
contains an actual simple source-supported route avoiding the old endpoint;
collision constructors remain explicit in the transition and satisfy only the
corresponding fail-closed branch.  Companion-rail separation, reconstruction
of a full two-rail assembly, rolling iteration, end caps, and Fable flag L1
remain open.
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

private abbrev BridgeLeft :=
  firstSuccessor.rightRailsAsNextLeft bridge

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

/-- The advanced result either clears the old face or supplies one of the four
literal old-rail/future-rail cross-splices.  New collision outcomes retain
their witness in `outcome` and make no success claim. -/
def ExactSelectedLocalRailFourCellRetainedOutcome.ResolvesFourthFarEndpointBySourceSplice
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
  | .straight assembly | .swapped assembly =>
      (face ∉ assembly.firstRail.support ∧
          face ∉ assembly.secondRail.support) ∨
        ((Nonempty (SecondBandFutureSourceSplice
              (corridor := corridor) (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext) (hfourthNext := hfourthNext)
              (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
              face (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.firstRail assembly.firstRail) ∨
            Nonempty (SecondBandFutureSourceSplice
              (corridor := corridor) (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext) (hfourthNext := hfourthNext)
              (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
              face (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.secondRail assembly.firstRail)) ∨
          (Nonempty (SecondBandFutureSourceSplice
              (corridor := corridor) (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext) (hfourthNext := hfourthNext)
              (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
              face (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.firstRail assembly.secondRail) ∨
            Nonempty (SecondBandFutureSourceSplice
              (corridor := corridor) (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext) (hfourthNext := hfourthNext)
              (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
              face (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.secondRail assembly.secondRail)))
  | .straightStraightCollision _ _ _ _ _
  | .straightSwappedCollision _ _ _ _ _
  | .swappedStraightCollision _ _ _ _ _
  | .swappedSwappedCollision _ _ _ _ _ => True

/-- **L1 canonical far-end consumption.**  The actual future transition
either retains its exact new collision, clears the old endpoint, or supplies
a literal simple source-supported splice avoiding that endpoint. -/
theorem SecondFourthFarEndpoint.canonicalFutureTransition_resolvesBySourceSplice
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {face : SelectedFace (web := web)}
    (endpoint : SecondFourthFarEndpoint
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (fourthPlacement := fourthPlacement) (lastSuccessor := lastSuccessor) face) :
    let transition :=
      SupportCertifiedExactSelectedLocalRailTracedFourCellTransition.ofClassifiers
        (firstSuccessor := fourthSuccessor) (bridge := fifthSuccessor)
        (lastSuccessor := sixthSuccessor)
        (firstLeft := FutureFirstLeft (lastSuccessor := lastSuccessor)
          (fourthSuccessor := fourthSuccessor)) hsource
    ExactSelectedLocalRailFourCellRetainedOutcome.ResolvesFourthFarEndpointBySourceSplice
      (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      transition.transition.outcome face := by
  let transition :=
    SupportCertifiedExactSelectedLocalRailTracedFourCellTransition.ofClassifiers
      (firstSuccessor := fourthSuccessor) (bridge := fifthSuccessor)
      (lastSuccessor := sixthSuccessor)
      (firstLeft := FutureFirstLeft (lastSuccessor := lastSuccessor)
        (fourthSuccessor := fourthSuccessor)) hsource
  change ExactSelectedLocalRailFourCellRetainedOutcome.ResolvesFourthFarEndpointBySourceSplice
    (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
    (firstSuccessor := firstSuccessor) (bridge := bridge)
    transition.transition.outcome face
  have hresolved := endpoint.canonicalFutureTransition_resolvesAtFinish
    (hfourthNext := hfourthNext) (hfifthNext := hfifthNext)
    (hsixthNext := hsixthNext) (fifthPlacement := fifthPlacement)
    (sixthPlacement := sixthPlacement) (seventhPlacement := seventhPlacement)
    (fourthSuccessor := fourthSuccessor) (fifthSuccessor := fifthSuccessor)
    (sixthSuccessor := sixthSuccessor) hsource
  change transition.transition.outcome.ResolvesFourthFarEndpointAtFinish face at hresolved
  have hprovenance := transition.hasWindowSupportProvenance
  have spliceNew
      {newStart newFinish : SelectedFace (web := web)}
      (newWalk : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk newStart newFinish)
      (hnewPath : newWalk.IsPath) (hnew : face ∈ newWalk.support)
      (hnewEnd : face ≠ newFinish)
      (hnewNear : ∀ current ∈ newWalk.support,
        FaceNearExactTerminalCenterPairs
          (corridor := corridor)
          (firstInterior := FourthInterior (firstInterior := firstInterior)
            (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
            (hlastNext := hlastNext))
          (hfirstNext := hfourthNext) (hbridgeNext := hfifthNext)
          (hlastNext := hsixthNext) current) :
      Nonempty (SecondBandFutureSourceSplice
          (corridor := corridor) (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
          (hlastNext := hlastNext) (hfourthNext := hfourthNext)
          (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
          face (BridgeLeft (firstSuccessor := firstSuccessor)
            (bridge := bridge)).paths.firstRail newWalk) ∨
        Nonempty (SecondBandFutureSourceSplice
          (corridor := corridor) (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
          (hlastNext := hlastNext) (hfourthNext := hfourthNext)
          (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
          face (BridgeLeft (firstSuccessor := firstSuccessor)
            (bridge := bridge)).paths.secondRail newWalk) := by
    rcases endpoint.oldOriginWithStart with first | second
    · exact .inl (endpoint.exists_secondBandFutureCrossSplice
        (BridgeLeft (firstSuccessor := firstSuccessor)
          (bridge := bridge)).paths.firstRail newWalk
        (BridgeLeft (firstSuccessor := firstSuccessor)
          (bridge := bridge)).paths.firstRail_isPath hnewPath
        first.1 hnew first.2 hnewEnd
        (BridgeLeft (firstSuccessor := firstSuccessor)
          (bridge := bridge)).paths.firstRail_support_adjacent_center hnewNear)
    · exact .inr (endpoint.exists_secondBandFutureCrossSplice
        (BridgeLeft (firstSuccessor := firstSuccessor)
          (bridge := bridge)).paths.secondRail newWalk
        (BridgeLeft (firstSuccessor := firstSuccessor)
          (bridge := bridge)).paths.secondRail_isPath hnewPath
        second.1 hnew second.2 hnewEnd
        (BridgeLeft (firstSuccessor := firstSuccessor)
          (bridge := bridge)).paths.secondRail_support_adjacent_center hnewNear)
  cases hresult : transition.transition.outcome with
  | straight assembly =>
      change
        (face ∉ assembly.firstRail.support ∧
            face ∉ assembly.secondRail.support) ∨ _
      have hfirstNear : ∀ current ∈ assembly.firstRail.support,
          FaceNearExactTerminalCenterPairs
            (corridor := corridor)
            (firstInterior := FourthInterior (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext))
            (hfirstNext := hfourthNext) (hbridgeNext := hfifthNext)
            (hlastNext := hsixthNext) current := by
        intro current hcurrent
        exact transition.transition.outcome.faceNearTerminalCenterPairs_of_contains
          hprovenance (by
            rw [hresult]
            exact .inl hcurrent)
      have hsecondNear : ∀ current ∈ assembly.secondRail.support,
          FaceNearExactTerminalCenterPairs
            (corridor := corridor)
            (firstInterior := FourthInterior (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext))
            (hfirstNext := hfourthNext) (hbridgeNext := hfifthNext)
            (hlastNext := hsixthNext) current := by
        intro current hcurrent
        exact transition.transition.outcome.faceNearTerminalCenterPairs_of_contains
          hprovenance (by
            rw [hresult]
            exact .inr hcurrent)
      rw [hresult] at hresolved
      rcases hresolved with hcleared | hfirst | hsecond
      · exact .inl hcleared
      · exact .inr (.inl (spliceNew assembly.firstRail assembly.firstRail_isPath
          hfirst.1 hfirst.2.2 hfirstNear))
      · exact .inr (.inr (spliceNew assembly.secondRail assembly.secondRail_isPath
          hsecond.2.1 hsecond.2.2 hsecondNear))
  | swapped assembly =>
      change
        (face ∉ assembly.firstRail.support ∧
            face ∉ assembly.secondRail.support) ∨ _
      have hfirstNear : ∀ current ∈ assembly.firstRail.support,
          FaceNearExactTerminalCenterPairs
            (corridor := corridor)
            (firstInterior := FourthInterior (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext))
            (hfirstNext := hfourthNext) (hbridgeNext := hfifthNext)
            (hlastNext := hsixthNext) current := by
        intro current hcurrent
        exact transition.transition.outcome.faceNearTerminalCenterPairs_of_contains
          hprovenance (by
            rw [hresult]
            exact .inl hcurrent)
      have hsecondNear : ∀ current ∈ assembly.secondRail.support,
          FaceNearExactTerminalCenterPairs
            (corridor := corridor)
            (firstInterior := FourthInterior (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext))
            (hfirstNext := hfourthNext) (hbridgeNext := hfifthNext)
            (hlastNext := hsixthNext) current := by
        intro current hcurrent
        exact transition.transition.outcome.faceNearTerminalCenterPairs_of_contains
          hprovenance (by
            rw [hresult]
            exact .inr hcurrent)
      rw [hresult] at hresolved
      rcases hresolved with hcleared | hfirst | hsecond
      · exact .inl hcleared
      · exact .inr (.inl (spliceNew assembly.firstRail assembly.firstRail_isPath
          hfirst.1 hfirst.2.2 hfirstNear))
      · exact .inr (.inr (spliceNew assembly.secondRail assembly.secondRail_isPath
          hsecond.2.1 hsecond.2.2 hsecondNear))
  | straightStraightCollision => trivial
  | straightSwappedCollision => trivial
  | swappedStraightCollision => trivial
  | swappedSwappedCollision => trivial

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
