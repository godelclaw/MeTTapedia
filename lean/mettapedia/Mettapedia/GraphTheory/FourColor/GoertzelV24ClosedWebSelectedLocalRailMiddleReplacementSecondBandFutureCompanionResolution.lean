import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSecondBandFutureCompanionPieces

/-!
# L1: classify the actual advanced companion splice

The canonical future transition already retains one of four literal
old/future source-splice choices.  The canonical middle classifier now tests
the companion route for that actual choice.  A compatible pairing returns a
complete companion path; an incompatible pairing returns the exact typed
parity mismatch.

This is an exhaustive classification of the successful future outcome, not a
repair of the mismatch.  New future collisions remain explicit.  Centre
avoidance, mutual separation, rolling iteration, end caps, the separated
crosscut pair, and Fable flag L1 remain open.
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

/-- One retained companion-piece packet is either completed by the canonical
middle classifier or accompanied by its exact parity mismatch. -/
def SecondBandFutureSourceSpliceCompanionPieces.ResolvesWithCanonicalMiddle
    {face oldStart oldFinish newStart newFinish
      oldCompanionStart oldCompanionFinish
      newCompanionStart newCompanionFinish : SelectedFace (web := web)}
    {oldWalk : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk oldStart oldFinish}
    {newWalk : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk newStart newFinish}
    {oldCompanion : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        oldCompanionStart oldCompanionFinish}
    {newCompanion : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        newCompanionStart newCompanionFinish}
    (pieces : SecondBandFutureSourceSpliceCompanionPieces
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
      (face := face) oldWalk newWalk oldCompanion newCompanion)
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)))
    (splicePairing : SourceSplicePairing) : Prop :=
  Nonempty (SecondBandFutureSourceSpliceCompanionRoute pieces) ∨
    Nonempty (SecondBandFutureSourceSpliceCompanionParityMismatch
      trace splicePairing)

/-- Successful future outcomes clear the old endpoint or retain one literal
source-splice packet classified against the actual canonical middle trace.
Collision constructors remain explicitly fail-closed. -/
def ExactSelectedLocalRailFourCellRetainedOutcome.ResolvesFourthFarEndpointWithCompanion
    (middleTrace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)))
    {firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      fourthSuccessor
      (FutureFirstLeft (lastSuccessor := lastSuccessor)
        (fourthSuccessor := fourthSuccessor))}
    {lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow sixthSuccessor
      (fifthSuccessor.rightRailsAsNextLeft sixthSuccessor)}
    (outcome : ExactSelectedLocalRailFourCellRetainedOutcome firstWindow lastWindow)
    (face : SelectedFace (web := web)) : Prop :=
  match outcome with
  | .straight assembly | .swapped assembly =>
      (face ∉ assembly.firstRail.support ∧
          face ∉ assembly.secondRail.support) ∨
        (((∃ pieces : SecondBandFutureSourceSpliceCompanionPieces
              (corridor := corridor) (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext) (hfourthNext := hfourthNext)
              (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
              (face := face)
              (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.firstRail assembly.firstRail
              (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.secondRail assembly.secondRail,
            pieces.ResolvesWithCanonicalMiddle middleTrace .straight) ∨
          (∃ pieces : SecondBandFutureSourceSpliceCompanionPieces
              (corridor := corridor) (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext) (hfourthNext := hfourthNext)
              (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
              (face := face)
              (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.secondRail assembly.firstRail
              (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.firstRail assembly.secondRail,
            pieces.ResolvesWithCanonicalMiddle middleTrace .swapped)) ∨
        ((∃ pieces : SecondBandFutureSourceSpliceCompanionPieces
              (corridor := corridor) (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext) (hfourthNext := hfourthNext)
              (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
              (face := face)
              (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.firstRail assembly.secondRail
              (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.secondRail assembly.firstRail,
            pieces.ResolvesWithCanonicalMiddle middleTrace .swapped) ∨
          (∃ pieces : SecondBandFutureSourceSpliceCompanionPieces
              (corridor := corridor) (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext) (hfourthNext := hfourthNext)
              (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
              (face := face)
              (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.secondRail assembly.secondRail
              (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.firstRail assembly.firstRail,
            pieces.ResolvesWithCanonicalMiddle middleTrace .straight)))
  | .straightStraightCollision _ _ _ _ _
  | .straightSwappedCollision _ _ _ _ _
  | .swappedStraightCollision _ _ _ _ _
  | .swappedSwappedCollision _ _ _ _ _ => True

/-- **L1 actual companion classification.**  The canonical future transition
and canonical middle classifier jointly return a companion route or the exact
pairing mismatch for every retained source splice. -/
theorem SecondFourthFarEndpoint.canonicalFutureTransition_resolvesWithCompanion
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
    let middleTrace := ExactSelectedLocalRailConstructionTrace.ofClassifier
      (successor := bridge)
      (left := BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))
    transition.transition.outcome.ResolvesFourthFarEndpointWithCompanion
      (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
      (firstSuccessor := firstSuccessor) (lastSuccessor := lastSuccessor)
      middleTrace face := by
  let transition :=
    SupportCertifiedExactSelectedLocalRailTracedFourCellTransition.ofClassifiers
      (firstSuccessor := fourthSuccessor) (bridge := fifthSuccessor)
      (lastSuccessor := sixthSuccessor)
      (firstLeft := FutureFirstLeft (lastSuccessor := lastSuccessor)
        (fourthSuccessor := fourthSuccessor)) hsource
  let middleTrace := ExactSelectedLocalRailConstructionTrace.ofClassifier
    (successor := bridge)
    (left := BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))
  change transition.transition.outcome.ResolvesFourthFarEndpointWithCompanion
    (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
    (firstSuccessor := firstSuccessor) (lastSuccessor := lastSuccessor)
    middleTrace face
  have hpieces := endpoint.canonicalFutureTransition_resolvesWithCompanionPieces
    (hfourthNext := hfourthNext) (hfifthNext := hfifthNext)
    (hsixthNext := hsixthNext) (fifthPlacement := fifthPlacement)
    (sixthPlacement := sixthPlacement) (seventhPlacement := seventhPlacement)
    (fourthSuccessor := fourthSuccessor) (fifthSuccessor := fifthSuccessor)
    (sixthSuccessor := sixthSuccessor) hsource
  change transition.transition.outcome.ResolvesFourthFarEndpointWithCompanionPieces
    (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
    (firstSuccessor := firstSuccessor) (bridge := bridge) face at hpieces
  cases hresult : transition.transition.outcome with
  | straight assembly =>
      rw [hresult] at hpieces
      change (face ∉ assembly.firstRail.support ∧
        face ∉ assembly.secondRail.support) ∨ _ at hpieces
      change (face ∉ assembly.firstRail.support ∧
        face ∉ assembly.secondRail.support) ∨ _
      rcases hpieces with hclear | hpieces
      · exact .inl hclear
      · rcases hpieces with (hfirstFirst | hsecondFirst) |
          (hfirstSecond | hsecondSecond)
        · rcases hfirstFirst with ⟨pieces⟩
          exact .inr (.inl (.inl ⟨pieces, pieces.resolve_firstFirst middleTrace⟩))
        · rcases hsecondFirst with ⟨pieces⟩
          exact .inr (.inl (.inr ⟨pieces, pieces.resolve_secondFirst middleTrace⟩))
        · rcases hfirstSecond with ⟨pieces⟩
          exact .inr (.inr (.inl ⟨pieces, pieces.resolve_firstSecond middleTrace⟩))
        · rcases hsecondSecond with ⟨pieces⟩
          exact .inr (.inr (.inr ⟨pieces, pieces.resolve_secondSecond middleTrace⟩))
  | swapped assembly =>
      rw [hresult] at hpieces
      change (face ∉ assembly.firstRail.support ∧
        face ∉ assembly.secondRail.support) ∨ _ at hpieces
      change (face ∉ assembly.firstRail.support ∧
        face ∉ assembly.secondRail.support) ∨ _
      rcases hpieces with hclear | hpieces
      · exact .inl hclear
      · rcases hpieces with (hfirstFirst | hsecondFirst) |
          (hfirstSecond | hsecondSecond)
        · rcases hfirstFirst with ⟨pieces⟩
          exact .inr (.inl (.inl ⟨pieces, pieces.resolve_firstFirst middleTrace⟩))
        · rcases hsecondFirst with ⟨pieces⟩
          exact .inr (.inl (.inr ⟨pieces, pieces.resolve_secondFirst middleTrace⟩))
        · rcases hfirstSecond with ⟨pieces⟩
          exact .inr (.inr (.inl ⟨pieces, pieces.resolve_firstSecond middleTrace⟩))
        · rcases hsecondSecond with ⟨pieces⟩
          exact .inr (.inr (.inr ⟨pieces, pieces.resolve_secondSecond middleTrace⟩))
  | straightStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      simp [ExactSelectedLocalRailFourCellRetainedOutcome.ResolvesFourthFarEndpointWithCompanion]
  | straightSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      simp [ExactSelectedLocalRailFourCellRetainedOutcome.ResolvesFourthFarEndpointWithCompanion]
  | swappedStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      simp [ExactSelectedLocalRailFourCellRetainedOutcome.ResolvesFourthFarEndpointWithCompanion]
  | swappedSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      simp [ExactSelectedLocalRailFourCellRetainedOutcome.ResolvesFourthFarEndpointWithCompanion]

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
