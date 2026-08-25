import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailFourCellSourceSquareCompanionSeparation

/-!
# L1: turn a four-cell source-square bypass into a repaired rail pair

The source-square classifier returns either a literal selected chord triangle
with a cyclic inner side or a whole-rail splice repair.  The four-cell support
calculation proves that the latter repair remains disjoint from the untouched
future rail.  This module consumes both results and reconstructs the actual
two-rail assembly, for both endpoint orders and either choice of repaired rail.

Thus the good source-square branch is no longer merely a repair certificate:
it is a new separated assembly with the same four endpoints.  The cyclic
chord-triangle alternative remains explicit.  This module does not eliminate
that alternative, discharge the two local no-double-edge premises, iterate the
rolling transition, attach end caps, construct separated crosscuts, or close
Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathPointedOccurrence
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
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

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

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

/-- Replace the first rail of an assembly by a whole-rail splice repair. -/
noncomputable def InteriorOccurrence.SpliceRepair.replaceFirstRailAssembly
    {firstStart secondStart firstFinish secondFinish current : SelectedFace
      (web := web)}
    {assembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart firstFinish secondFinish}
    {occurrence : InteriorOccurrence (current := current) assembly.firstRail}
    {bypass : InteriorOccurrence.TwoHopBypass occurrence}
    (repair : InteriorOccurrence.SpliceRepair occurrence bypass)
    (hdisjoint : repair.walk.support.Disjoint assembly.secondRail.support) :
    SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart firstFinish secondFinish where
  firstRail := repair.walk
  secondRail := assembly.secondRail
  firstRail_isPath := repair.isPath
  secondRail_isPath := assembly.secondRail_isPath
  firstRail_support_disjoint_secondRail := hdisjoint

/-- Replace the second rail of an assembly by a whole-rail splice repair. -/
noncomputable def InteriorOccurrence.SpliceRepair.replaceSecondRailAssembly
    {firstStart secondStart firstFinish secondFinish current : SelectedFace
      (web := web)}
    {assembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart firstFinish secondFinish}
    {occurrence : InteriorOccurrence (current := current) assembly.secondRail}
    {bypass : InteriorOccurrence.TwoHopBypass occurrence}
    (repair : InteriorOccurrence.SpliceRepair occurrence bypass)
    (hdisjoint : assembly.firstRail.support.Disjoint repair.walk.support) :
    SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart firstFinish secondFinish where
  firstRail := assembly.firstRail
  secondRail := repair.walk
  firstRail_isPath := assembly.firstRail_isPath
  secondRail_isPath := repair.isPath
  firstRail_support_disjoint_secondRail := hdisjoint

/-- The exact cyclic residue returned by the source-square classifier. -/
def SourceSquareChordTriangleCycle
    {face : SelectedFace (web := web)}
    (hfirst : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hthird : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) : Prop :=
  let square := MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
    (rungs := rungs) hfirst hthird hfaceSecond
  ∃ selected : square.SourceChordSelectedTriangles
      (secondPlacement := secondPlacement),
    (∃ component :
        (G.deleteEdges (edgeFinsetValueSet
          selected.firstShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
      web.annular.RS.outer.fst ∉ component.supp ∧
        HasCycleOnSide G (fun vertex => vertex ∈ component.supp)) ∨
      ∃ component :
        (G.deleteEdges (edgeFinsetValueSet
          selected.secondShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
      web.annular.RS.outer.fst ∉ component.supp ∧
        HasCycleOnSide G (fun vertex => vertex ∈ component.supp)

private theorem exists_sourceSquare_cycle_or_repairedFirstAssembly
    {assembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
      firstFinish secondFinish}
    {face : SelectedFace (web := web)}
    {occurrence : InteriorOccurrence (current := face) assembly.firstRail}
    (allocation : InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
      occurrence)
    (hfirst : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hsecond : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hthird : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    (successor : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement)
    (hneBefore : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftBefore)
    (hneAfter : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftAfter)
    (hrepair : ∀ {bypass : InteriorOccurrence.SourceSquareTwoHopBypass
        (corridor := corridor) (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext) occurrence},
      (repair : InteriorOccurrence.SpliceRepair occurrence bypass.toTwoHopBypass) →
        repair.walk.support.Disjoint assembly.secondRail.support) :
    SourceSquareChordTriangleCycle (rungs := rungs)
        (secondPlacement := secondPlacement) hfirst hthird hfaceSecond ∨
      Nonempty (SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
        (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
        firstFinish secondFinish) := by
  rcases allocation.exists_sourceSquare_chordTriangleCycle_or_spliceRepair
      assembly.firstRail_isPath hfirst hsecond hthird hfaceSecond successor
      hneBefore hneAfter with hcycle | ⟨bypass, ⟨repair⟩⟩
  · exact .inl hcycle
  · exact .inr ⟨repair.replaceFirstRailAssembly (hrepair repair)⟩

private theorem exists_sourceSquare_cycle_or_repairedSecondAssembly
    {assembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
      firstFinish secondFinish}
    {face : SelectedFace (web := web)}
    {occurrence : InteriorOccurrence (current := face) assembly.secondRail}
    (allocation : InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
      occurrence)
    (hfirst : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hsecond : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hthird : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    (successor : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement)
    (hneBefore : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftBefore)
    (hneAfter : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftAfter)
    (hrepair : ∀ {bypass : InteriorOccurrence.SourceSquareTwoHopBypass
        (corridor := corridor) (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext) occurrence},
      (repair : InteriorOccurrence.SpliceRepair occurrence bypass.toTwoHopBypass) →
        assembly.firstRail.support.Disjoint repair.walk.support) :
    SourceSquareChordTriangleCycle (rungs := rungs)
        (secondPlacement := secondPlacement) hfirst hthird hfaceSecond ∨
      Nonempty (SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
        (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
        firstFinish secondFinish) := by
  rcases allocation.exists_sourceSquare_chordTriangleCycle_or_spliceRepair
      assembly.secondRail_isPath hfirst hsecond hthird hfaceSecond successor
      hneBefore hneAfter with hcycle | ⟨bypass, ⟨repair⟩⟩
  · exact .inl hcycle
  · exact .inr ⟨repair.replaceSecondRailAssembly (hrepair repair)⟩

/-- **L1 straight/first repair outcome.**  Repairing the first rail of a
successful straight future yields a new separated assembly unless the source
square exhibits the explicit cyclic chord-triangle residue. -/
theorem InteriorOccurrence.SelectedAdjacentPointedFaceAllocation.exists_sourceSquare_cycle_or_repairedFirstAssembly_of_shiftedStraight
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
    (allocation : InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
      occurrence)
    (hfirst : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hsecond : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hthird : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    (successor : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement)
    (hneBefore : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftBefore)
    (hneAfter : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftAfter)
    (hfirstCard : ShiftedFirstNoDouble
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext))
    (hsecondCard : ShiftedSecondNoDouble
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext)) :
    SourceSquareChordTriangleCycle (rungs := rungs)
        (secondPlacement := secondPlacement) hfirst hthird hfaceSecond ∨
      Nonempty (ShiftedStraightAssembly
        (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
        (fifthPlacement := fifthPlacement) (firstSuccessor := firstSuccessor)
        (fourthSuccessor := fourthSuccessor)) := by
  apply exists_sourceSquare_cycle_or_repairedFirstAssembly allocation hfirst
    hsecond hthird hfaceSecond successor hneBefore hneAfter
  intro bypass repair
  exact repair.support_disjoint_secondRail_of_shiftedStraight future assembly
    houtcome hfirstCard hsecondCard

/-- **L1 straight/second repair outcome.**  The companion orientation is
preserved when the second rail of a straight future is repaired. -/
theorem InteriorOccurrence.SelectedAdjacentPointedFaceAllocation.exists_sourceSquare_cycle_or_repairedSecondAssembly_of_shiftedStraight
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
    (allocation : InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
      occurrence)
    (hfirst : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hsecond : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hthird : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    (successor : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement)
    (hneBefore : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftBefore)
    (hneAfter : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftAfter)
    (hfirstCard : ShiftedFirstNoDouble
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext))
    (hsecondCard : ShiftedSecondNoDouble
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext)) :
    SourceSquareChordTriangleCycle (rungs := rungs)
        (secondPlacement := secondPlacement) hfirst hthird hfaceSecond ∨
      Nonempty (ShiftedStraightAssembly
        (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
        (fifthPlacement := fifthPlacement) (firstSuccessor := firstSuccessor)
        (fourthSuccessor := fourthSuccessor)) := by
  apply exists_sourceSquare_cycle_or_repairedSecondAssembly allocation hfirst
    hsecond hthird hfaceSecond successor hneBefore hneAfter
  intro bypass repair
  exact (repair.support_disjoint_firstRail_of_shiftedStraight future assembly
    houtcome hfirstCard hsecondCard).symm

/-- **L1 swapped/first repair outcome.**  Repairing the first rail of a
successful swapped future preserves that swapped endpoint order. -/
theorem InteriorOccurrence.SelectedAdjacentPointedFaceAllocation.exists_sourceSquare_cycle_or_repairedFirstAssembly_of_shiftedSwapped
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
    (allocation : InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
      occurrence)
    (hfirst : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hsecond : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hthird : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    (successor : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement)
    (hneBefore : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftBefore)
    (hneAfter : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftAfter)
    (hfirstCard : ShiftedFirstNoDouble
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext))
    (hsecondCard : ShiftedSecondNoDouble
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext)) :
    SourceSquareChordTriangleCycle (rungs := rungs)
        (secondPlacement := secondPlacement) hfirst hthird hfaceSecond ∨
      Nonempty (ShiftedSwappedAssembly
        (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
        (fifthPlacement := fifthPlacement) (firstSuccessor := firstSuccessor)
        (fourthSuccessor := fourthSuccessor)) := by
  apply exists_sourceSquare_cycle_or_repairedFirstAssembly allocation hfirst
    hsecond hthird hfaceSecond successor hneBefore hneAfter
  intro bypass repair
  exact repair.support_disjoint_secondRail_of_shiftedSwapped future assembly
    houtcome hfirstCard hsecondCard

/-- **L1 swapped/second repair outcome.**  The final source-square case also
returns an actual separated assembly, rather than a bare repair certificate. -/
theorem InteriorOccurrence.SelectedAdjacentPointedFaceAllocation.exists_sourceSquare_cycle_or_repairedSecondAssembly_of_shiftedSwapped
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
    (allocation : InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
      occurrence)
    (hfirst : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hsecond : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hthird : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    (successor : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement)
    (hneBefore : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftBefore)
    (hneAfter : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftAfter)
    (hfirstCard : ShiftedFirstNoDouble
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext))
    (hsecondCard : ShiftedSecondNoDouble
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext)) :
    SourceSquareChordTriangleCycle (rungs := rungs)
        (secondPlacement := secondPlacement) hfirst hthird hfaceSecond ∨
      Nonempty (ShiftedSwappedAssembly
        (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
        (fifthPlacement := fifthPlacement) (firstSuccessor := firstSuccessor)
        (fourthSuccessor := fourthSuccessor)) := by
  apply exists_sourceSquare_cycle_or_repairedSecondAssembly allocation hfirst
    hsecond hthird hfaceSecond successor hneBefore hneAfter
  intro bypass repair
  exact (repair.support_disjoint_firstRail_of_shiftedSwapped future assembly
    houtcome hfirstCard hsecondCard).symm

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
