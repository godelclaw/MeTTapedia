import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementBoundedSuffixState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailTracedFourCellSupport

/-!
# L1: align the bounded live suffix with one common future span

The raw bounded-suffix step distinguishes a clean adjacent append from a
collision followed by a wider middle replacement.  Those two witnesses have
different endpoint spans, so they cannot themselves be the next rolling
state.

The canonical support-certified four-cell transition on the shifted window
already has one common span.  This module constructs that transition beside
the raw step and proves the two overlap receipts which make it the same live
calculation: its first trace is the old suffix's later trace, and its bridge
trace is the newly classified trace of the shifted suffix.

The result is a constructed common-span packet, not a flattening theorem.  A
successful future outcome still has to be joined to the retained one-cell
connector, and every future collision remains explicit.  No prefix is frozen,
no end cap or dual crosscut is constructed, and Fable flag L1 remains open.
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
    {hfourthNext :
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext).center.val + 2 < blockLength}
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
    {fifthPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext)
        hfourthNext)}
    {firstSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfirstNext
      firstPlacement secondPlacement}
    {bridge : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement}
    {lastSuccessor : SeparatedSelectedSourceLocalRailSuccessor hlastNext
      thirdPlacement fourthPlacement}
    {fourthSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfourthNext
      fourthPlacement fifthPlacement}
    {firstIncomingBefore firstIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions firstPlacement}}
    {firstLeft : SeparatedSelectedSourceLocalRailPaths firstPlacement
      firstIncomingBefore firstIncomingAfter firstSuccessor.frame.leftBefore
      firstSuccessor.frame.leftAfter}

private abbrev ShiftedLive
    (live : BoundedLiveTracePair
      (leftInterior := firstInterior)
      (hfirstNext := hfirstNext) (hsecondNext := hbridgeNext)
      (leftPlacement := firstPlacement) (middlePlacement := secondPlacement)
      (rightPlacement := thirdPlacement)
      (firstSuccessor := firstSuccessor) (secondSuccessor := bridge) firstLeft) :=
  live.advance
    (hthirdNext := hlastNext) (fourthPlacement := fourthPlacement)
    (thirdSuccessor := lastSuccessor)

/-- The raw seam classification and the canonical common-span future
transition, tied together by their two literal overlapping traces. -/
structure BoundedLiveCommonSpanTransition
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (live : BoundedLiveTracePair
      (leftInterior := firstInterior)
      (hfirstNext := hfirstNext) (hsecondNext := hbridgeNext)
      (leftPlacement := firstPlacement) (middlePlacement := secondPlacement)
      (rightPlacement := thirdPlacement)
      (firstSuccessor := firstSuccessor) (secondSuccessor := bridge) firstLeft) where
  rawAdvance : BoundedLiveTracePair.RepairAdvanceOutcome
    (lastSuccessor := lastSuccessor)
    (hfourthNext := hfourthNext) (fifthPlacement := fifthPlacement)
    (fourthSuccessor := fourthSuccessor) live
  rawAdvance_eq : rawAdvance = BoundedLiveTracePair.classifyRepairAdvance
    (lastSuccessor := lastSuccessor)
    (hfourthNext := hfourthNext) (fifthPlacement := fifthPlacement)
    (fourthSuccessor := fourthSuccessor) live
  future : SupportCertifiedExactSelectedLocalRailTracedFourCellTransition
    (firstInterior := nextCorridorInterior firstInterior hfirstNext)
    (hfirstNext := hbridgeNext) (hbridgeNext := hlastNext)
    (hlastNext := hfourthNext)
    (firstPlacement := secondPlacement) (secondPlacement := thirdPlacement)
    (thirdPlacement := fourthPlacement) (fourthPlacement := fifthPlacement)
    (firstSuccessor := bridge) (bridge := lastSuccessor)
    (lastSuccessor := fourthSuccessor)
    (firstLeft := firstSuccessor.rightRailsAsNextLeft bridge)
  future_eq : future =
    SupportCertifiedExactSelectedLocalRailTracedFourCellTransition.ofClassifiers
      (firstInterior := nextCorridorInterior firstInterior hfirstNext)
      (hfirstNext := hbridgeNext) (hbridgeNext := hlastNext)
      (hlastNext := hfourthNext)
      (firstPlacement := secondPlacement) (secondPlacement := thirdPlacement)
      (thirdPlacement := fourthPlacement) (fourthPlacement := fifthPlacement)
      (firstSuccessor := bridge) (bridge := lastSuccessor)
      (lastSuccessor := fourthSuccessor)
      (firstLeft := firstSuccessor.rightRailsAsNextLeft bridge)
      hsource
  firstTrace_eq : future.transition.firstTrace = live.laterTrace
  bridgeTrace_eq : future.transition.bridgeTrace = (ShiftedLive live).laterTrace

namespace BoundedLiveCommonSpanTransition

/-- **L1 constructed common-span receipt.**  Run both actual classifiers and
identify their overlapping traces.  The support-certified future outcome is
therefore attached to the existing bounded live suffix rather than being an
unrelated inhabitant with the same endpoint types. -/
noncomputable def ofClassifiers
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (live : BoundedLiveTracePair
      (leftInterior := firstInterior)
      (hfirstNext := hfirstNext) (hsecondNext := hbridgeNext)
      (leftPlacement := firstPlacement) (middlePlacement := secondPlacement)
      (rightPlacement := thirdPlacement)
      (firstSuccessor := firstSuccessor) (secondSuccessor := bridge) firstLeft) :
    BoundedLiveCommonSpanTransition
      (lastSuccessor := lastSuccessor)
      (hfourthNext := hfourthNext) (fifthPlacement := fifthPlacement)
      (fourthSuccessor := fourthSuccessor) hsource live := by
  let rawAdvance := BoundedLiveTracePair.classifyRepairAdvance
    (lastSuccessor := lastSuccessor)
    (hfourthNext := hfourthNext) (fifthPlacement := fifthPlacement)
    (fourthSuccessor := fourthSuccessor) live
  let future :=
    SupportCertifiedExactSelectedLocalRailTracedFourCellTransition.ofClassifiers
      (firstInterior := nextCorridorInterior firstInterior hfirstNext)
      (hfirstNext := hbridgeNext) (hbridgeNext := hlastNext)
      (hlastNext := hfourthNext)
      (firstPlacement := secondPlacement) (secondPlacement := thirdPlacement)
      (thirdPlacement := fourthPlacement) (fourthPlacement := fifthPlacement)
      (firstSuccessor := bridge) (bridge := lastSuccessor)
      (lastSuccessor := fourthSuccessor)
      (firstLeft := firstSuccessor.rightRailsAsNextLeft bridge) hsource
  exact
    { rawAdvance := rawAdvance
      rawAdvance_eq := rfl
      future := future
      future_eq := rfl
      firstTrace_eq := ExactSelectedLocalRailConstructionTrace.eq_of_same _ _
      bridgeTrace_eq := ExactSelectedLocalRailConstructionTrace.eq_of_same _ _ }

end BoundedLiveCommonSpanTransition

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
