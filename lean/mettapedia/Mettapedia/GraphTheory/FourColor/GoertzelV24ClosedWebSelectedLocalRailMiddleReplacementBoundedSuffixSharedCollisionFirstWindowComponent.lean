import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementBoundedSuffixSharedCollisionFirstWindowSeparator
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareBond

/-!
# L1: construct the star or bond behind the shared-collision separator

The first-window separator packet classifies its boundary-free component by
cardinality.  This module turns those numerical alternatives into the actual
source objects: a common star vertex incident to every crossing of a selected
triangle, or a two-vertex square bond carrying every crossing of a selected
quadrilateral.  The cyclic alternative remains explicit.

This is constructive component geometry.  It does not eliminate a cyclic
side, identify the star with a particular rail endpoint, apply the local bond
bypass to both rails, iterate the rolling transition, attach end caps, build
crosscuts, or close Fable flag L1.
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

/-- Constructive form of the component trichotomy behind a selected short
separator. -/
inductive RetainedSharedCollisionSeparatorComponentResolution
    {face : SelectedFace (web := web)}
    (receipt : RetainedSharedCollisionShortSeparatorReceipt
      (web := web) face) : Type (u + 1)
  | cyclic
      (hasCycle : HasCycleOnSide G
        (fun vertex => vertex ∈ receipt.component.supp))
  | star
      (vertex : V)
      (mem_component : vertex ∈ receipt.component.supp)
      (incident_all : ∀ edge ∈ receipt.cycle.selectedCycle.crossingEdges,
        vertex ∈ edge.1)
  | bond
      (realization :
        MiddleReplacementShortDualCycle.SquareBondRealization
          receipt.cycle receipt.component)

/-- Replace the two acyclic cardinality alternatives by their literal star
and bond witnesses. -/
theorem RetainedSharedCollisionShortSeparatorReceipt.toComponentResolution
    {face : SelectedFace (web := web)}
    (receipt : RetainedSharedCollisionShortSeparatorReceipt
      (web := web) face) :
    Nonempty (RetainedSharedCollisionSeparatorComponentResolution receipt) := by
  rcases receipt.componentGeometry with hcycle | hstar | hbond
  · exact ⟨.cyclic hcycle⟩
  · rcases receipt.cycle.exists_vertex_mem_all_crossingEdges_of_component_card_eq_one
        receipt.component receipt.outerRoot_not_mem hstar.1 with
      ⟨vertex, hmem, hall⟩
    exact ⟨.star vertex hmem hall⟩
  · obtain ⟨first, second, hne, hsupp, hadj, hcover⟩ :=
      receipt.cycle.exists_adjacent_pair_covering_crossingEdges_of_component_card_eq_two
        receipt.component receipt.outerRoot_not_mem hbond.1
    exact ⟨.bond {
      first := first
      second := second
      first_ne_second := hne
      component_supp := hsupp
      adjacent := hadj
      covers_crossingEdges := hcover
    }⟩

/-- Source packet plus fully constructed component geometry. -/
structure RetainedSharedCollisionFirstWindowComponentResolution
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
      ∃ receipt : RetainedSharedCollisionShortSeparatorReceipt
          (web := web) face,
        Nonempty (RetainedSharedCollisionSeparatorComponentResolution receipt)

/-- Strengthen the separator packet to the exact cyclic/star/bond objects. -/
theorem RetainedSharedCollisionFirstWindowSeparatorResolution.toComponentResolution
    {future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor)}
    {face : SelectedFace (web := web)}
    (resolution : RetainedSharedCollisionFirstWindowSeparatorResolution
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (firstLeft := firstLeft) future face) :
    RetainedSharedCollisionFirstWindowComponentResolution
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (firstLeft := firstLeft) future face := by
  refine ⟨resolution.sourceData, ?_⟩
  rcases resolution.physical with hcenter | hreceipt
  · exact .inl hcenter
  · rcases hreceipt with ⟨receipt⟩
    exact .inr ⟨receipt, receipt.toComponentResolution⟩

/-- Outcome-level constructive component receipt. -/
def BoundedLiveSharedRailAppendOutcome.HasFirstWindowComponentResolution
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
      RetainedSharedCollisionFirstWindowComponentResolution
        (corridor := corridor) (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
        (hlastNext := hlastNext) (hfourthNext := hfourthNext)
        (firstLeft := firstLeft) future collision.face

/-- **L1 bounded component resolution.** Every newly retained collision now
returns a centre, a cyclic component, a literal common star vertex, or a
literal square bond.  No branch is assumed away. -/
theorem BoundedLiveSharedRailAppendTransition.hasFirstWindowComponentResolution
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
    transition.outcome.HasFirstWindowComponentResolution transition.frozen
      transition.common.future := by
  have hseparator := transition.hasFirstWindowSeparatorResolution
  cases houtcome : transition.outcome with
  | straight assembly => trivial
  | swapped assembly => trivial
  | futureCollision collision =>
      rw [houtcome] at hseparator
      exact hseparator
  | retainedStraightCollision futureAssembly hfuture collision =>
      rw [houtcome] at hseparator
      exact hseparator.toComponentResolution
  | retainedSwappedCollision futureAssembly hfuture collision =>
      rw [houtcome] at hseparator
      exact hseparator.toComponentResolution

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
