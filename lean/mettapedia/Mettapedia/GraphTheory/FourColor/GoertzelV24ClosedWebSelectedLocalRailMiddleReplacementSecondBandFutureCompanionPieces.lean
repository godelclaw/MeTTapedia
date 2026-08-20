import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSecondBandFutureSpliceResolution

/-!
# L1: retain the complementary source pieces of the advanced splice

The advanced endpoint repair chooses one old rail and one successful future
rail for its centre-chain splice.  The other rail of each separated source
pair must not be forgotten: those two complementary pieces are the endpoints
of the companion-rail construction.

This module refines all four parity branches with those literal companion
pieces and their already-proved source-pair disjointness.  In each pairing
compatible with the canonical middle classifier it joins the companion pieces
into a complete path; in each incompatible pairing it retains a typed parity
mismatch.  It does not yet eliminate that mismatch, prove avoidance of the
intervening corridor centres, rebuild a separated two-rail assembly, iterate
the rolling transition, attach end caps, or close Fable flag L1.
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

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

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

/-- One advanced source splice together with the two literal source pieces
which must be joined to form its companion rail.  The two disjointness fields
come from the old and future separated pairs; only the middle join remains. -/
structure SecondBandFutureSourceSpliceCompanionPieces
    {face oldStart oldFinish newStart newFinish
      oldCompanionStart oldCompanionFinish
      newCompanionStart newCompanionFinish : SelectedFace (web := web)}
    (oldWalk : SelectedDualGraph (web := web).Walk oldStart oldFinish)
    (newWalk : SelectedDualGraph (web := web).Walk newStart newFinish)
    (oldCompanion : SelectedDualGraph (web := web).Walk
      oldCompanionStart oldCompanionFinish)
    (newCompanion : SelectedDualGraph (web := web).Walk
      newCompanionStart newCompanionFinish) where
  splice : SecondBandFutureSourceSplice
    (corridor := corridor) (firstInterior := firstInterior)
    (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
    (hlastNext := hlastNext) (hfourthNext := hfourthNext)
    (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
    face oldWalk newWalk
  old_disjoint : oldWalk.support.Disjoint oldCompanion.support
  new_disjoint : newWalk.support.Disjoint newCompanion.support

/-- A complete companion walk obtained by joining the middle classifier's
opposite rail to the retained future companion piece.  The route is loop
erased, and its support receipt remembers the two literal inputs.  Separation
from the primary splice is deliberately not a field here. -/
structure SecondBandFutureSourceSpliceCompanionRoute
    {face oldStart oldFinish newStart newFinish
      oldCompanionStart oldCompanionFinish
      newCompanionStart newCompanionFinish : SelectedFace (web := web)}
    {oldWalk : SelectedDualGraph (web := web).Walk oldStart oldFinish}
    {newWalk : SelectedDualGraph (web := web).Walk newStart newFinish}
    {oldCompanion : SelectedDualGraph (web := web).Walk
      oldCompanionStart oldCompanionFinish}
    {newCompanion : SelectedDualGraph (web := web).Walk
      newCompanionStart newCompanionFinish}
    (pieces : SecondBandFutureSourceSpliceCompanionPieces
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
      (face := face)
      oldWalk newWalk oldCompanion newCompanion) where
  middle : SelectedDualGraph (web := web).Walk
    oldCompanionStart newCompanionStart
  middle_isPath : middle.IsPath
  route : SelectedDualGraph (web := web).Walk
    oldCompanionStart newCompanionFinish
  route_isPath : route.IsPath
  support_receipt : ∀ current ∈ route.support,
    current ∈ middle.support ∨ current ∈ newCompanion.support

/-- Append and loop erase a literal middle connector and future source piece.
This is the algebraic constructor used by the four source-parity lemmas below. -/
noncomputable def SecondBandFutureSourceSpliceCompanionRoute.ofMiddle
    {face oldStart oldFinish newStart newFinish
      oldCompanionStart oldCompanionFinish
      newCompanionStart newCompanionFinish : SelectedFace (web := web)}
    {oldWalk : SelectedDualGraph (web := web).Walk oldStart oldFinish}
    {newWalk : SelectedDualGraph (web := web).Walk newStart newFinish}
    {oldCompanion : SelectedDualGraph (web := web).Walk
      oldCompanionStart oldCompanionFinish}
    {newCompanion : SelectedDualGraph (web := web).Walk
      newCompanionStart newCompanionFinish}
    (pieces : SecondBandFutureSourceSpliceCompanionPieces
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
      (face := face)
      oldWalk newWalk oldCompanion newCompanion)
    (middle : SelectedDualGraph (web := web).Walk
      oldCompanionStart newCompanionStart)
    (hmiddle : middle.IsPath) :
    SecondBandFutureSourceSpliceCompanionRoute pieces := by
  let raw := middle.append newCompanion
  refine {
    middle := middle
    middle_isPath := hmiddle
    route := raw.bypass
    route_isPath := raw.bypass_isPath
    support_receipt := ?_
  }
  intro current hcurrent
  have hraw := raw.support_bypass_subset_support hcurrent
  rw [SimpleGraph.Walk.support_append] at hraw
  rcases List.mem_append.mp hraw with hmiddleCurrent | hnewCurrent
  · exact .inl hmiddleCurrent
  · exact .inr (List.mem_of_mem_tail hnewCurrent)

private abbrev MiddleStraightAssembly :=
  SelectedSourceLocalRailAssembly (web := web)
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
    (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore)
    (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter)

private abbrev MiddleSwappedAssembly :=
  SelectedSourceLocalRailAssembly (web := web)
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
    (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter)
    (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore)

/-- The two endpoint pairings visible to the companion splice.  `straight`
means first-to-first and second-to-second; `swapped` means first-to-second and
second-to-first. -/
inductive SourceSplicePairing
  | straight
  | swapped
  deriving DecidableEq

/-- Proof-relevant parity read from the actual canonical middle classifier.
The assembly is retained so later repairs can use its literal rails rather
than merely a Boolean tag. -/
inductive ExactCanonicalMiddlePairing
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))) :
    SourceSplicePairing -> Prop
  | straight
      (middle : MiddleStraightAssembly (firstSuccessor := firstSuccessor)
        (bridge := bridge))
      (hresult : trace.toOutcome = .straight middle) :
      ExactCanonicalMiddlePairing trace .straight
  | swapped
      (middle : MiddleSwappedAssembly (firstSuccessor := firstSuccessor)
        (bridge := bridge))
      (hresult : trace.toOutcome = .swapped middle) :
      ExactCanonicalMiddlePairing trace .swapped

/-- A fail-closed parity residue.  It records the exact middle-classifier
branch and proves that it differs from the retained primary splice pairing.
It is data for the rolling repair, not a successful companion route. -/
structure SecondBandFutureSourceSpliceCompanionParityMismatch
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)))
    (splicePairing : SourceSplicePairing) where
  middlePairing : SourceSplicePairing
  exactMiddle : ExactCanonicalMiddlePairing trace middlePairing
  incompatible : middlePairing ≠ splicePairing

/-- Straight middle parity joins the opposite second track in a first/first
source splice to the future second track. -/
noncomputable def SecondBandFutureSourceSpliceCompanionPieces.route_firstFirst_of_straight
    {face newFirstFinish newSecondFinish : SelectedFace (web := web)}
    {newFirst : SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace fourthPlacement lastSuccessor.frame.rightAfter)
      newFirstFinish}
    {newSecond : SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace fourthPlacement lastSuccessor.frame.rightBefore)
      newSecondFinish}
    (pieces : SecondBandFutureSourceSpliceCompanionPieces
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
      (face := face)
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.firstRail newFirst
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.secondRail newSecond)
    (middle : MiddleStraightAssembly (firstSuccessor := firstSuccessor)
      (bridge := bridge)) :
    SecondBandFutureSourceSpliceCompanionRoute pieces :=
  SecondBandFutureSourceSpliceCompanionRoute.ofMiddle pieces
    (middle.secondRail.copy rfl
      (bridge.rightOutgoingAfterFace_eq_nextRightBeforeFace lastSuccessor))
    (by simpa using middle.secondRail_isPath)

/-- Straight middle parity joins the opposite first track in a second/second
source splice to the future first track. -/
noncomputable def SecondBandFutureSourceSpliceCompanionPieces.route_secondSecond_of_straight
    {face newFirstFinish newSecondFinish : SelectedFace (web := web)}
    {newFirst : SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace fourthPlacement lastSuccessor.frame.rightAfter)
      newFirstFinish}
    {newSecond : SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace fourthPlacement lastSuccessor.frame.rightBefore)
      newSecondFinish}
    (pieces : SecondBandFutureSourceSpliceCompanionPieces
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
      (face := face)
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.secondRail newSecond
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.firstRail newFirst)
    (middle : MiddleStraightAssembly (firstSuccessor := firstSuccessor)
      (bridge := bridge)) :
    SecondBandFutureSourceSpliceCompanionRoute pieces :=
  SecondBandFutureSourceSpliceCompanionRoute.ofMiddle pieces
    (middle.firstRail.copy rfl
      (bridge.rightOutgoingBeforeFace_eq_nextRightAfterFace lastSuccessor))
    (by simpa using middle.firstRail_isPath)

/-- Swapped middle parity joins the opposite second track in a first/second
source splice to the future first track. -/
noncomputable def SecondBandFutureSourceSpliceCompanionPieces.route_firstSecond_of_swapped
    {face newFirstFinish newSecondFinish : SelectedFace (web := web)}
    {newFirst : SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace fourthPlacement lastSuccessor.frame.rightAfter)
      newFirstFinish}
    {newSecond : SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace fourthPlacement lastSuccessor.frame.rightBefore)
      newSecondFinish}
    (pieces : SecondBandFutureSourceSpliceCompanionPieces
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
      (face := face)
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.firstRail newSecond
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.secondRail newFirst)
    (middle : MiddleSwappedAssembly (firstSuccessor := firstSuccessor)
      (bridge := bridge)) :
    SecondBandFutureSourceSpliceCompanionRoute pieces :=
  SecondBandFutureSourceSpliceCompanionRoute.ofMiddle pieces
    (middle.secondRail.copy rfl
      (bridge.rightOutgoingBeforeFace_eq_nextRightAfterFace lastSuccessor))
    (by simpa using middle.secondRail_isPath)

/-- Swapped middle parity joins the opposite first track in a second/first
source splice to the future second track. -/
noncomputable def SecondBandFutureSourceSpliceCompanionPieces.route_secondFirst_of_swapped
    {face newFirstFinish newSecondFinish : SelectedFace (web := web)}
    {newFirst : SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace fourthPlacement lastSuccessor.frame.rightAfter)
      newFirstFinish}
    {newSecond : SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace fourthPlacement lastSuccessor.frame.rightBefore)
      newSecondFinish}
    (pieces : SecondBandFutureSourceSpliceCompanionPieces
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
      (face := face)
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.secondRail newFirst
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.firstRail newSecond)
    (middle : MiddleSwappedAssembly (firstSuccessor := firstSuccessor)
      (bridge := bridge)) :
    SecondBandFutureSourceSpliceCompanionRoute pieces :=
  SecondBandFutureSourceSpliceCompanionRoute.ofMiddle pieces
    (middle.firstRail.copy rfl
      (bridge.rightOutgoingAfterFace_eq_nextRightBeforeFace lastSuccessor))
    (by simpa using middle.firstRail_isPath)

/-- The canonical middle classifier either completes a first/first primary
splice or returns its exact swapped-parity residue. -/
theorem SecondBandFutureSourceSpliceCompanionPieces.resolve_firstFirst
    {face newFirstFinish newSecondFinish : SelectedFace (web := web)}
    {newFirst : SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace fourthPlacement lastSuccessor.frame.rightAfter)
      newFirstFinish}
    {newSecond : SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace fourthPlacement lastSuccessor.frame.rightBefore)
      newSecondFinish}
    (pieces : SecondBandFutureSourceSpliceCompanionPieces
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
      (face := face)
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.firstRail newFirst
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.secondRail newSecond)
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))) :
    Nonempty (SecondBandFutureSourceSpliceCompanionRoute pieces) ∨
      Nonempty (SecondBandFutureSourceSpliceCompanionParityMismatch trace .straight) := by
  cases hresult : trace.toOutcome with
  | straight middle =>
      exact .inl ⟨pieces.route_firstFirst_of_straight middle⟩
  | swapped middle =>
      exact .inr ⟨⟨.swapped, .swapped middle hresult, by decide⟩⟩

/-- The canonical middle classifier either completes a second/second primary
splice or returns its exact swapped-parity residue. -/
theorem SecondBandFutureSourceSpliceCompanionPieces.resolve_secondSecond
    {face newFirstFinish newSecondFinish : SelectedFace (web := web)}
    {newFirst : SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace fourthPlacement lastSuccessor.frame.rightAfter)
      newFirstFinish}
    {newSecond : SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace fourthPlacement lastSuccessor.frame.rightBefore)
      newSecondFinish}
    (pieces : SecondBandFutureSourceSpliceCompanionPieces
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
      (face := face)
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.secondRail newSecond
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.firstRail newFirst)
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))) :
    Nonempty (SecondBandFutureSourceSpliceCompanionRoute pieces) ∨
      Nonempty (SecondBandFutureSourceSpliceCompanionParityMismatch trace .straight) := by
  cases hresult : trace.toOutcome with
  | straight middle =>
      exact .inl ⟨pieces.route_secondSecond_of_straight middle⟩
  | swapped middle =>
      exact .inr ⟨⟨.swapped, .swapped middle hresult, by decide⟩⟩

/-- The canonical middle classifier either completes a first/second primary
splice or returns its exact straight-parity residue. -/
theorem SecondBandFutureSourceSpliceCompanionPieces.resolve_firstSecond
    {face newFirstFinish newSecondFinish : SelectedFace (web := web)}
    {newFirst : SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace fourthPlacement lastSuccessor.frame.rightAfter)
      newFirstFinish}
    {newSecond : SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace fourthPlacement lastSuccessor.frame.rightBefore)
      newSecondFinish}
    (pieces : SecondBandFutureSourceSpliceCompanionPieces
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
      (face := face)
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.firstRail newSecond
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.secondRail newFirst)
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))) :
    Nonempty (SecondBandFutureSourceSpliceCompanionRoute pieces) ∨
      Nonempty (SecondBandFutureSourceSpliceCompanionParityMismatch trace .swapped) := by
  cases hresult : trace.toOutcome with
  | straight middle =>
      exact .inr ⟨⟨.straight, .straight middle hresult, by decide⟩⟩
  | swapped middle =>
      exact .inl ⟨pieces.route_firstSecond_of_swapped middle⟩

/-- The canonical middle classifier either completes a second/first primary
splice or returns its exact straight-parity residue. -/
theorem SecondBandFutureSourceSpliceCompanionPieces.resolve_secondFirst
    {face newFirstFinish newSecondFinish : SelectedFace (web := web)}
    {newFirst : SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace fourthPlacement lastSuccessor.frame.rightAfter)
      newFirstFinish}
    {newSecond : SelectedDualGraph (web := web).Walk
      (selectedPlacementSideFace fourthPlacement lastSuccessor.frame.rightBefore)
      newSecondFinish}
    (pieces : SecondBandFutureSourceSpliceCompanionPieces
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
      (face := face)
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.secondRail newFirst
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.firstRail newSecond)
    (trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))) :
    Nonempty (SecondBandFutureSourceSpliceCompanionRoute pieces) ∨
      Nonempty (SecondBandFutureSourceSpliceCompanionParityMismatch trace .swapped) := by
  cases hresult : trace.toOutcome with
  | straight middle =>
      exact .inr ⟨⟨.straight, .straight middle hresult, by decide⟩⟩
  | swapped middle =>
      exact .inl ⟨pieces.route_secondFirst_of_swapped middle⟩

/-- Successful future outcomes either clear the old endpoint or retain one of
the four exact source-splice parities together with the complementary source
pieces.  Collision constructors remain explicitly fail-closed. -/
def ExactSelectedLocalRailFourCellRetainedOutcome.ResolvesFourthFarEndpointWithCompanionPieces
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
        ((Nonempty (SecondBandFutureSourceSpliceCompanionPieces
              (corridor := corridor) (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext) (hfourthNext := hfourthNext)
              (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
              (face := face)
              (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.firstRail assembly.firstRail
              (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.secondRail assembly.secondRail) ∨
            Nonempty (SecondBandFutureSourceSpliceCompanionPieces
              (corridor := corridor) (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext) (hfourthNext := hfourthNext)
              (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
              (face := face)
              (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.secondRail assembly.firstRail
              (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.firstRail assembly.secondRail)) ∨
          (Nonempty (SecondBandFutureSourceSpliceCompanionPieces
              (corridor := corridor) (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext) (hfourthNext := hfourthNext)
              (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
              (face := face)
              (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.firstRail assembly.secondRail
              (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.secondRail assembly.firstRail) ∨
            Nonempty (SecondBandFutureSourceSpliceCompanionPieces
              (corridor := corridor) (firstInterior := firstInterior)
              (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
              (hlastNext := hlastNext) (hfourthNext := hfourthNext)
              (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
              (face := face)
              (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.secondRail assembly.secondRail
              (BridgeLeft (firstSuccessor := firstSuccessor)
                (bridge := bridge)).paths.firstRail assembly.firstRail)))
  | .straightStraightCollision _ _ _ _ _
  | .straightSwappedCollision _ _ _ _ _
  | .swappedStraightCollision _ _ _ _ _
  | .swappedSwappedCollision _ _ _ _ _ => True

/-- **L1 complementary-piece retention.**  The actual future transition keeps
the source pieces complementary to every constructed advanced splice, together
with the disjointness already proved inside the two selected rail pairs. -/
theorem SecondFourthFarEndpoint.canonicalFutureTransition_resolvesWithCompanionPieces
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
    ExactSelectedLocalRailFourCellRetainedOutcome.ResolvesFourthFarEndpointWithCompanionPieces
      (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      transition.transition.outcome face := by
  let transition :=
    SupportCertifiedExactSelectedLocalRailTracedFourCellTransition.ofClassifiers
      (firstSuccessor := fourthSuccessor) (bridge := fifthSuccessor)
      (lastSuccessor := sixthSuccessor)
      (firstLeft := FutureFirstLeft (lastSuccessor := lastSuccessor)
        (fourthSuccessor := fourthSuccessor)) hsource
  change ExactSelectedLocalRailFourCellRetainedOutcome.ResolvesFourthFarEndpointWithCompanionPieces
    (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
    (firstSuccessor := firstSuccessor) (bridge := bridge)
    transition.transition.outcome face
  have hresolved := endpoint.canonicalFutureTransition_resolvesBySourceSplice
    (hfourthNext := hfourthNext) (hfifthNext := hfifthNext)
    (hsixthNext := hsixthNext) (fifthPlacement := fifthPlacement)
    (sixthPlacement := sixthPlacement) (seventhPlacement := seventhPlacement)
    (fourthSuccessor := fourthSuccessor) (fifthSuccessor := fifthSuccessor)
    (sixthSuccessor := sixthSuccessor) hsource
  change transition.transition.outcome.ResolvesFourthFarEndpointBySourceSplice face
    at hresolved
  cases hresult : transition.transition.outcome with
  | straight assembly =>
      rw [hresult] at hresolved
      change (face ∉ assembly.firstRail.support ∧
          face ∉ assembly.secondRail.support) ∨ _
      change (face ∉ assembly.firstRail.support ∧
          face ∉ assembly.secondRail.support) ∨ _ at hresolved
      rcases hresolved with hclear | hsplices
      · exact .inl hclear
      · rcases hsplices with (hfirstFirst | hsecondFirst) |
          (hfirstSecond | hsecondSecond)
        · rcases hfirstFirst with ⟨splice⟩
          exact .inr (.inl (.inl ⟨splice,
            (BridgeLeft (firstSuccessor := firstSuccessor)
              (bridge := bridge)).firstRail_support_disjoint_secondRail,
            assembly.firstRail_support_disjoint_secondRail⟩))
        · rcases hsecondFirst with ⟨splice⟩
          exact .inr (.inl (.inr ⟨splice,
            (BridgeLeft (firstSuccessor := firstSuccessor)
              (bridge := bridge)).firstRail_support_disjoint_secondRail.symm,
            assembly.firstRail_support_disjoint_secondRail⟩))
        · rcases hfirstSecond with ⟨splice⟩
          exact .inr (.inr (.inl ⟨splice,
            (BridgeLeft (firstSuccessor := firstSuccessor)
              (bridge := bridge)).firstRail_support_disjoint_secondRail,
            assembly.firstRail_support_disjoint_secondRail.symm⟩))
        · rcases hsecondSecond with ⟨splice⟩
          exact .inr (.inr (.inr ⟨splice,
            (BridgeLeft (firstSuccessor := firstSuccessor)
              (bridge := bridge)).firstRail_support_disjoint_secondRail.symm,
            assembly.firstRail_support_disjoint_secondRail.symm⟩))
  | swapped assembly =>
      rw [hresult] at hresolved
      change (face ∉ assembly.firstRail.support ∧
          face ∉ assembly.secondRail.support) ∨ _
      change (face ∉ assembly.firstRail.support ∧
          face ∉ assembly.secondRail.support) ∨ _ at hresolved
      rcases hresolved with hclear | hsplices
      · exact .inl hclear
      · rcases hsplices with (hfirstFirst | hsecondFirst) |
          (hfirstSecond | hsecondSecond)
        · rcases hfirstFirst with ⟨splice⟩
          exact .inr (.inl (.inl ⟨splice,
            (BridgeLeft (firstSuccessor := firstSuccessor)
              (bridge := bridge)).firstRail_support_disjoint_secondRail,
            assembly.firstRail_support_disjoint_secondRail⟩))
        · rcases hsecondFirst with ⟨splice⟩
          exact .inr (.inl (.inr ⟨splice,
            (BridgeLeft (firstSuccessor := firstSuccessor)
              (bridge := bridge)).firstRail_support_disjoint_secondRail.symm,
            assembly.firstRail_support_disjoint_secondRail⟩))
        · rcases hfirstSecond with ⟨splice⟩
          exact .inr (.inr (.inl ⟨splice,
            (BridgeLeft (firstSuccessor := firstSuccessor)
              (bridge := bridge)).firstRail_support_disjoint_secondRail,
            assembly.firstRail_support_disjoint_secondRail.symm⟩))
        · rcases hsecondSecond with ⟨splice⟩
          exact .inr (.inr (.inr ⟨splice,
            (BridgeLeft (firstSuccessor := firstSuccessor)
              (bridge := bridge)).firstRail_support_disjoint_secondRail.symm,
            assembly.firstRail_support_disjoint_secondRail.symm⟩))
  | straightStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      simp [ExactSelectedLocalRailFourCellRetainedOutcome.ResolvesFourthFarEndpointWithCompanionPieces]
  | straightSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      simp [ExactSelectedLocalRailFourCellRetainedOutcome.ResolvesFourthFarEndpointWithCompanionPieces]
  | swappedStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      simp [ExactSelectedLocalRailFourCellRetainedOutcome.ResolvesFourthFarEndpointWithCompanionPieces]
  | swappedSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      simp [ExactSelectedLocalRailFourCellRetainedOutcome.ResolvesFourthFarEndpointWithCompanionPieces]

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
