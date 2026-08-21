import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailFourCellMiddleCenterAvoidance
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeSourceSquareBypassSplice

/-!
# L1: preserve the successful four-cell companion through a source-square repair

The retained shared-prefix collision lives on one rail of the successful
shifted four-cell future.  A source-square bypass repairs that rail by adding
only the displayed third Cell--3 centre.  The other future rail was already
support-disjoint, and the terminal-window provenance calculation proves that
it avoids this centre under the two local no-double-edge conditions.

This module composes those two facts for both endpoint orders and both choices
of repaired rail.  It does not prove the local cardinality premises, eliminate
their double-edge branches, construct the rolling transition or its end caps,
construct separated crosscuts, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathPointedOccurrence
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

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev ShiftedFuture :=
  SupportCertifiedExactSelectedLocalRailTracedFourCellTransition
    (firstInterior := nextCorridorInterior firstInterior hfirstNext)
    (hfirstNext := hbridgeNext) (hbridgeNext := hlastNext)
    (hlastNext := hfourthNext)
    (firstPlacement := secondPlacement) (secondPlacement := thirdPlacement)
    (thirdPlacement := fourthPlacement) (fourthPlacement := fifthPlacement)
    (firstSuccessor := bridge) (bridge := lastSuccessor)
    (lastSuccessor := fourthSuccessor)
    (firstLeft := firstSuccessor.rightRailsAsNextLeft bridge)

private abbrev ShiftedStraightAssembly :=
  SelectedSourceLocalRailAssembly (web := web)
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
    (selectedPlacementSideFace fifthPlacement
      fourthSuccessor.rightOutgoingBefore)
    (selectedPlacementSideFace fifthPlacement
      fourthSuccessor.rightOutgoingAfter)

private abbrev ShiftedSwappedAssembly :=
  SelectedSourceLocalRailAssembly (web := web)
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
    (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
    (selectedPlacementSideFace fifthPlacement
      fourthSuccessor.rightOutgoingAfter)
    (selectedPlacementSideFace fifthPlacement
      fourthSuccessor.rightOutgoingBefore)

private abbrev ShiftedFirstNoDouble : Prop :=
  (sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))
    ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
      (nextCorridorInterior firstInterior hfirstNext).center).1
    ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center).1).card
      ≤ 1

private abbrev ShiftedSecondNoDouble : Prop :=
  (sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))
    ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center).1
    ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext).center).1).card ≤ 1

/-- Repairing the first rail of a straight shifted future preserves
separation from its second rail. -/
theorem InteriorOccurrence.SpliceRepair.support_disjoint_secondRail_of_shiftedStraight
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor))
    (assembly : ShiftedStraightAssembly
      (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
      (fifthPlacement := fifthPlacement) (firstSuccessor := firstSuccessor)
      (fourthSuccessor := fourthSuccessor))
    (houtcome : future.transition.outcome = .straight assembly)
    {face : SelectedFace (web := web)}
    {occurrence : InteriorOccurrence (current := face) assembly.firstRail}
    {bypass : InteriorOccurrence.SourceSquareTwoHopBypass
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext) occurrence}
    (repair : InteriorOccurrence.SpliceRepair occurrence bypass.toTwoHopBypass)
    (hfirstCard : ShiftedFirstNoDouble
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext))
    (hsecondCard : ShiftedSecondNoDouble
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext)) :
    repair.walk.support.Disjoint assembly.secondRail.support := by
  have hcenters := future.secondCenter_not_mem_straight_supports_of_card_le_one
    assembly houtcome hfirstCard hsecondCard
  exact repair.support_disjoint_companion_of_sourceSquare
    assembly.firstRail_support_disjoint_secondRail hcenters.2

/-- Repairing the second rail of a straight shifted future preserves
separation from its first rail. -/
theorem InteriorOccurrence.SpliceRepair.support_disjoint_firstRail_of_shiftedStraight
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor))
    (assembly : ShiftedStraightAssembly
      (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
      (fifthPlacement := fifthPlacement) (firstSuccessor := firstSuccessor)
      (fourthSuccessor := fourthSuccessor))
    (houtcome : future.transition.outcome = .straight assembly)
    {face : SelectedFace (web := web)}
    {occurrence : InteriorOccurrence (current := face) assembly.secondRail}
    {bypass : InteriorOccurrence.SourceSquareTwoHopBypass
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext) occurrence}
    (repair : InteriorOccurrence.SpliceRepair occurrence bypass.toTwoHopBypass)
    (hfirstCard : ShiftedFirstNoDouble
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext))
    (hsecondCard : ShiftedSecondNoDouble
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext)) :
    repair.walk.support.Disjoint assembly.firstRail.support := by
  have hcenters := future.secondCenter_not_mem_straight_supports_of_card_le_one
    assembly houtcome hfirstCard hsecondCard
  exact repair.support_disjoint_companion_of_sourceSquare
    assembly.firstRail_support_disjoint_secondRail.symm hcenters.1

/-- Repairing the first rail of a swapped shifted future preserves
separation from its second rail. -/
theorem InteriorOccurrence.SpliceRepair.support_disjoint_secondRail_of_shiftedSwapped
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor))
    (assembly : ShiftedSwappedAssembly
      (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
      (fifthPlacement := fifthPlacement) (firstSuccessor := firstSuccessor)
      (fourthSuccessor := fourthSuccessor))
    (houtcome : future.transition.outcome = .swapped assembly)
    {face : SelectedFace (web := web)}
    {occurrence : InteriorOccurrence (current := face) assembly.firstRail}
    {bypass : InteriorOccurrence.SourceSquareTwoHopBypass
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext) occurrence}
    (repair : InteriorOccurrence.SpliceRepair occurrence bypass.toTwoHopBypass)
    (hfirstCard : ShiftedFirstNoDouble
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext))
    (hsecondCard : ShiftedSecondNoDouble
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext)) :
    repair.walk.support.Disjoint assembly.secondRail.support := by
  have hcenters := future.secondCenter_not_mem_swapped_supports_of_card_le_one
    assembly houtcome hfirstCard hsecondCard
  exact repair.support_disjoint_companion_of_sourceSquare
    assembly.firstRail_support_disjoint_secondRail hcenters.2

/-- Repairing the second rail of a swapped shifted future preserves
separation from its first rail. -/
theorem InteriorOccurrence.SpliceRepair.support_disjoint_firstRail_of_shiftedSwapped
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor))
    (assembly : ShiftedSwappedAssembly
      (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
      (fifthPlacement := fifthPlacement) (firstSuccessor := firstSuccessor)
      (fourthSuccessor := fourthSuccessor))
    (houtcome : future.transition.outcome = .swapped assembly)
    {face : SelectedFace (web := web)}
    {occurrence : InteriorOccurrence (current := face) assembly.secondRail}
    {bypass : InteriorOccurrence.SourceSquareTwoHopBypass
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext) occurrence}
    (repair : InteriorOccurrence.SpliceRepair occurrence bypass.toTwoHopBypass)
    (hfirstCard : ShiftedFirstNoDouble
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext))
    (hsecondCard : ShiftedSecondNoDouble
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext)) :
    repair.walk.support.Disjoint assembly.firstRail.support := by
  have hcenters := future.secondCenter_not_mem_swapped_supports_of_card_le_one
    assembly houtcome hfirstCard hsecondCard
  exact repair.support_disjoint_companion_of_sourceSquare
    assembly.firstRail_support_disjoint_secondRail.symm hcenters.1

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
