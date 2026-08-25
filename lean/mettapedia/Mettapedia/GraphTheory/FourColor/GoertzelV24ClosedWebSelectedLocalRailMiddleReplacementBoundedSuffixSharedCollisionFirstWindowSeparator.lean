import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementBoundedSuffixSharedCollisionFirstWindowGeometry
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementComponent

/-!
# L1: realize the remaining shared collision as a small separator

The surviving retained-prefix collision is already confined to the first
three source cells and normalized to a centre, triangle, or square.  This
module consumes that geometry with the existing short-cycle separator API.

The centre case remains explicit.  Every non-centre case now carries an
actual selected primal cut of cardinality three or four, disjoint from both
named hole boundaries, whose deletion disconnects the annular carrier.  A
chosen component away from the outer root is classified exactly as cyclic, a
one-vertex star behind three crossings, or a two-vertex bond behind four.

This is a physical separator and component receipt.  It does not eliminate a
cyclic side, choose the surviving star/bond reroute, repair both rails, iterate
the rolling transition, attach end caps, construct crosscuts, or close Fable
flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open SimpleGraph

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

/-- Complete physical receipt for the selected short separator supplied by a
non-centre first-window collision. -/
structure RetainedSharedCollisionShortSeparatorReceipt
    (face : SelectedFace (web := web)) where
  cycle : MiddleReplacementShortDualCycle (web := web) face
  component :
    (G.deleteEdges (edgeFinsetValueSet
      cycle.selectedCycle.crossingEdges)).ConnectedComponent
  outerRoot_not_mem : web.annular.RS.outer.fst ∉ component.supp
  cut_card : cycle.selectedCycle.crossingEdges.card = 3 ∨
    cycle.selectedCycle.crossingEdges.card = 4
  disjoint_inner : Disjoint cycle.selectedCycle.crossingEdges
    (orbitFaceBoundary web.annular.RS web.annular.cellulation.innerHole)
  disjoint_outer : Disjoint cycle.selectedCycle.crossingEdges
    (orbitFaceBoundary web.annular.RS web.annular.cellulation.outerHole)
  disconnects :
    ¬ (G.deleteEdges (edgeFinsetValueSet
      cycle.selectedCycle.crossingEdges)).Connected
  componentGeometry :
    HasCycleOnSide G (fun vertex => vertex ∈ component.supp) ∨
      (Nat.card {vertex : V // vertex ∈ component.supp} = 1 ∧
        cycle.selectedCycle.crossingEdges.card = 3) ∨
      (Nat.card {vertex : V // vertex ∈ component.supp} = 2 ∧
        cycle.selectedCycle.crossingEdges.card = 4)

/-- Select the component away from the outer root and attach every existing
separator and locally cubic component receipt. -/
theorem MiddleReplacementShortDualCycle.exists_sharedCollisionSeparatorReceipt
    {face : SelectedFace (web := web)}
    (cycle : MiddleReplacementShortDualCycle (web := web) face) :
    Nonempty (RetainedSharedCollisionShortSeparatorReceipt
      (web := web) face) := by
  rcases cycle.exists_component_away_from_outerRoot with ⟨component, hroot⟩
  exact ⟨{
    cycle := cycle
    component := component
    outerRoot_not_mem := hroot
    cut_card := cycle.crossingEdges_card_eq_three_or_four
    disjoint_inner := cycle.crossingEdges_disjoint_innerHoleBoundary
    disjoint_outer := cycle.crossingEdges_disjoint_outerHoleBoundary
    disconnects := cycle.not_connected_deleteEdges_crossingEdges
    componentGeometry := cycle.hasCycleOnSide_or_component_star_or_bond
      component hroot
  }⟩

/-- The provenance-preserving form of the separator constructor.  The
returned receipt records definitionally that its selected cycle is the input
cycle; the older `Nonempty` interface intentionally forgets this equality. -/
theorem MiddleReplacementShortDualCycle.exists_sharedCollisionSeparatorReceipt_eq
    {face : SelectedFace (web := web)}
    (cycle : MiddleReplacementShortDualCycle (web := web) face) :
    ∃ receipt : RetainedSharedCollisionShortSeparatorReceipt
        (web := web) face,
      receipt.cycle = cycle := by
  rcases cycle.exists_component_away_from_outerRoot with ⟨component, hroot⟩
  exact ⟨{
    cycle := cycle
    component := component
    outerRoot_not_mem := hroot
    cut_card := cycle.crossingEdges_card_eq_three_or_four
    disjoint_inner := cycle.crossingEdges_disjoint_innerHoleBoundary
    disjoint_outer := cycle.crossingEdges_disjoint_outerHoleBoundary
    disconnects := cycle.not_connected_deleteEdges_crossingEdges
    componentGeometry := cycle.hasCycleOnSide_or_component_star_or_bond
      component hroot
  }, rfl⟩

/-- **L1 source-tied square separator.**  The first--third square branch
retains its literal ladder coordinates when it is promoted to a physical
separator.  In particular, the separator cycle is definitionally the
four-step cycle constructed from the two corridor edges and the collision
face; it is not an unrelated short cycle reconstructed after the source
classification has been forgotten.

This is provenance for the finite square case, not a rail repair or an L1
closure theorem. -/
theorem exists_firstThirdSquare_sharedCollisionSeparatorReceipt
    (selectedRungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton)
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
        (nextCorridorInterior firstInterior hfirstNext).center) :
    ∃ square : MiddleReplacementSquareDualCycle (web := web) face,
      ∃ receipt : RetainedSharedCollisionShortSeparatorReceipt
          (web := web) face,
        receipt.cycle = square.cycle := by
  let square := squareDualCycle_of_firstThirdSquare (rungs := selectedRungs)
    hfirst hthird hfaceSecond
  rcases square.cycle.exists_sharedCollisionSeparatorReceipt_eq with
    ⟨receipt, hreceipt⟩
  exact ⟨square, receipt, hreceipt⟩

/-- The exact source packet together with either the surviving centre or the
complete physical short-separator receipt. -/
structure RetainedSharedCollisionFirstWindowSeparatorResolution
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor))
    (face : SelectedFace (web := web)) : Prop where
  sourceData : RetainedSharedCollisionFirstWindowData
    (corridor := corridor) (firstInterior := firstInterior)
    (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
    (hlastNext := hlastNext) (hfourthNext := hfourthNext)
    (firstLeft := firstLeft) future face
  physical :
    face = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center ∨
      Nonempty (RetainedSharedCollisionShortSeparatorReceipt
        (web := web) face)

/-- **L1 first-window separator realization.**  The non-centre residue is an
actual small primal separator, not merely a facial-dual picture. -/
theorem RetainedSharedCollisionFirstWindowResolution.toSeparatorResolution
    {future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor)}
    {face : SelectedFace (web := web)}
    (resolution : RetainedSharedCollisionFirstWindowResolution
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (firstLeft := firstLeft) future face) :
    RetainedSharedCollisionFirstWindowSeparatorResolution
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (firstLeft := firstLeft) future face := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let third :=
    (nextCorridorInterior
      (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
  refine ⟨resolution.sourceData, ?_⟩
  rcases resolution.ladderGeometry.center_or_shortCycle (rungs := rungs) with
      hsecond | hthird | hcycle
  · exact .inl hsecond
  · have hfirstAdjacent : SelectedDualGraph (web := web).Adj
        (skeleton.faceAt firstInterior.center) face := by
      rcases resolution.sourceData.firstLive with hfirst | hsecond
      · exact firstLeft.paths.firstRail_support_adjacent_center face hfirst
      · exact firstLeft.paths.secondRail_support_adjacent_center face hsecond
    subst face
    exact False.elim ((skeleton.separated_not_adjacent
      firstInterior.center third (by dsimp [third]; omega)) hfirstAdjacent)
  · rcases hcycle with ⟨cycle⟩
    exact .inr cycle.exists_sharedCollisionSeparatorReceipt

/-- Outcome-level strengthening of the bounded append receipt. -/
def BoundedLiveSharedRailAppendOutcome.HasFirstWindowSeparatorResolution
    {firstStart secondStart : SelectedFace (web := web)}
    {prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter)}
    (frozen : SourceTiedBoundedLiveSharedRailPrefix
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (firstSuccessor := firstSuccessor)
      (firstIncomingBefore := firstIncomingBefore)
      (firstIncomingAfter := firstIncomingAfter) (firstLeft := firstLeft)
      prefixAssembly)
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor))
    (outcome : BoundedLiveSharedRailAppendOutcome frozen.toBounded future) : Prop :=
  match outcome with
  | .straight _ | .swapped _ => True
  | .futureCollision _ =>
      ∃ face : SelectedFace (web := web),
        ExactSelectedLocalRailFourCellCollisionBandWithMiddleTrace
          future.transition face
  | .retainedStraightCollision _ _ collision
  | .retainedSwappedCollision _ _ collision =>
      RetainedSharedCollisionFirstWindowSeparatorResolution
        (corridor := corridor) (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
        (hlastNext := hlastNext) (hfourthNext := hfourthNext)
        (firstLeft := firstLeft) future collision.face

/-- **L1 bounded separator receipt.**  Every newly retained collision is now
either the one displayed centre or a literal small separator with its exact
component trichotomy.  Future-internal collision bands remain explicit. -/
theorem BoundedLiveSharedRailAppendTransition.hasFirstWindowSeparatorResolution
    {firstStart secondStart : SelectedFace (web := web)}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter))
    (state : BoundedLiveMiddleReplacementState
      (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext)
      (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
      (thirdPlacement := thirdPlacement) (fourthPlacement := fourthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
      prefixAssembly)
    (transition : BoundedLiveSharedRailAppendTransition
      (hfourthNext := hfourthNext) (fifthPlacement := fifthPlacement)
      (fourthSuccessor := fourthSuccessor) prefixAssembly state) :
    transition.outcome.HasFirstWindowSeparatorResolution transition.frozen
      transition.common.future := by
  have hgeometry := transition.hasResolvedCollisionGeometry
  cases houtcome : transition.outcome with
  | straight assembly => trivial
  | swapped assembly => trivial
  | futureCollision collision =>
      rw [houtcome] at hgeometry
      exact hgeometry
  | retainedStraightCollision futureAssembly hfuture collision =>
      rw [houtcome] at hgeometry
      exact hgeometry.toSeparatorResolution
  | retainedSwappedCollision futureAssembly hfuture collision =>
      rw [houtcome] at hgeometry
      exact hgeometry.toSeparatorResolution

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
