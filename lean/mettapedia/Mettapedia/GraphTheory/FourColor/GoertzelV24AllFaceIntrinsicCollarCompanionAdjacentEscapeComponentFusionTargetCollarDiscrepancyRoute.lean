import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentFusionTargetCollarColorContact
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionSupportComponent

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CorridorPumping
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {W : Type u} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj]

/-- In a finite graph of maximum degree two, every edge either shares its
component with an odd vertex or lies on a simple cycle.  In the cycle branch
the displayed cycle contains the chosen edge itself. -/
theorem exists_odd_reachable_from_edge_or_cycle_through_edge_of_degree_le_two
    (edge : H.edgeSet) (hdegree : ∀ vertex : W, H.degree vertex ≤ 2) :
    (∃ start finish : W,
        start ∈ edge.1 ∧ Odd (H.degree finish) ∧ H.Reachable start finish) ∨
      ∃ (root : W) (cycle : H.Walk root root),
        root ∈ edge.1 ∧ cycle.IsCycle ∧ edge.1 ∈ cycle.edges := by
  classical
  rcases Sym2.mk_surjective (edge.1 : Sym2 W) with
    ⟨⟨first, second⟩, hedgeValue⟩
  have hedgeValue' : s(first, second) = edge.1 := hedgeValue
  have hadjacent : H.Adj first second := by
    apply (SimpleGraph.mem_edgeSet H).mp
    rw [hedgeValue']
    exact edge.2
  have hfirstMem : first ∈ edge.1 := by
    rw [← hedgeValue']
    exact Sym2.mem_mk_left first second
  have hpositive : 0 < H.degree first :=
    SimpleGraph.degree_pos_iff_nonempty.mpr ⟨second, hadjacent⟩
  have hdegreeCases : H.degree first = 1 ∨ H.degree first = 2 := by
    have hupper := hdegree first
    omega
  rcases hdegreeCases with hdegreeOne | hdegreeTwo
  · apply Or.inl
    exact ⟨first, first, hfirstMem, by simp [hdegreeOne],
      SimpleGraph.Reachable.refl first⟩
  · rcases exists_reachable_odd_or_cycle_of_degree_eq_two_of_degree_le_two
        first hdegreeTwo hdegree with hodd | hcycle
    · rcases hodd with ⟨finish, _hfinishNe, hfinishOdd, hreachable⟩
      exact Or.inl ⟨first, finish, hfirstMem, hfinishOdd, hreachable⟩
    · rcases hcycle with ⟨cycle, cycleIsCycle⟩
      exact Or.inr ⟨first, cycle, hfirstMem, cycleIsCycle,
        edge_mem_rooted_isCycle_of_degree_eq_two
          cycleIsCycle hdegreeTwo edge hfirstMem⟩

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

namespace IntrinsicShortTargetEscapeCollar

variable {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}

/-- A nonzero discrepancy contact routed through one scalar support
component to a named source or target port. -/
structure CommonDiscrepancyContactRoute
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : collar.commonCore.edgeSet) where
  coordinate : Bool
  coordinate_support : crossFaceCoordinate coordinate
    (collar.commonDiscrepancy sourceEscape edge) ≠ 0
  start : collar.commonCoreVertex
  start_mem_edge : start ∈ edge.1
  finish : collar.commonCoreVertex
  finish_mem_boundarySupport : finish ∈
    collar.commonDiscrepancyBoundarySupport sourceEscape
  reachable : (collar.coordinateDiscrepancySupportGraph
    sourceEscape coordinate).Reachable start finish

namespace CommonDiscrepancyContactRoute

variable {edge : collar.commonCore.edgeSet}
  (route : CommonDiscrepancyContactRoute collar sourceEscape edge)

/-- A charged discrepancy endpoint is one of the at-most-eight named collar
ports. -/
theorem finish_mem_commonPort :
    route.finish ∈ collar.commonPortVertexFinset :=
  collar.commonDiscrepancyBoundarySupport_subset_commonPortVertexFinset
    sourceEscape route.finish_mem_boundarySupport

end CommonDiscrepancyContactRoute

/-- A nonzero discrepancy contact lying on a closed scalar support
component.  The simple support cycle contains the contacted edge. -/
structure CommonDiscrepancyContactCycle
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : collar.commonCore.edgeSet) where
  coordinate : Bool
  coordinate_support : crossFaceCoordinate coordinate
    (collar.commonDiscrepancy sourceEscape edge) ≠ 0
  root : collar.commonCoreVertex
  root_mem_edge : root ∈ edge.1
  supportCycle : (collar.coordinateDiscrepancySupportGraph
    sourceEscape coordinate).Walk root root
  supportCycle_isCycle : supportCycle.IsCycle
  edge_mem_supportCycle : edge.1 ∈ supportCycle.edges

/-- Every nonzero common-core discrepancy contact reaches the finite named
port interface in one scalar coordinate, or belongs to a closed simple
support cycle in that coordinate. -/
theorem nonempty_commonDiscrepancyContactRoute_or_cycle
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : collar.commonCore.edgeSet)
    (hdiscrepancy : collar.commonDiscrepancy sourceEscape edge ≠ 0) :
    Nonempty (CommonDiscrepancyContactRoute collar sourceEscape edge) ∨
      Nonempty (CommonDiscrepancyContactCycle collar sourceEscape edge) := by
  rcases exists_crossFaceCoordinate_ne_zero
      (collar.commonDiscrepancy sourceEscape edge) hdiscrepancy with
    ⟨coordinate, hcoordinate⟩
  let supportGraph := collar.coordinateDiscrepancySupportGraph
    sourceEscape coordinate
  let supportEdge := collar.coordinateDiscrepancySupportEdge
    sourceEscape coordinate edge hcoordinate
  have hdegree : ∀ vertex : collar.commonCoreVertex,
      supportGraph.degree vertex ≤ 2 := by
    intro vertex
    rw [← incidentEdgeFinset_card_eq_degree]
    exact taitDiscrepancySupport_incidentCard_le_two
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait coordinate vertex
      (collar.commonCore_incidentEdgeFinset_card_le_three vertex)
  have hoddBoundarySupport : ∀ vertex : collar.commonCoreVertex,
      Odd (supportGraph.degree vertex) →
        vertex ∈ collar.commonDiscrepancyBoundarySupport sourceEscape := by
    intro vertex hodd
    have hscalarBoundary :
        scalarVertexKirchhoffSum collar.commonCore
          (fun current => crossFaceCoordinate coordinate
            (collar.commonDiscrepancy sourceEscape current)) vertex ≠ 0 :=
      (scalarSupportGraph_degree_odd_iff _ vertex).1 hodd
    have hboundary : vertexKirchhoffSum collar.commonCore
        (collar.commonDiscrepancy sourceEscape) vertex ≠ 0 := by
      intro hzero
      apply hscalarBoundary
      rw [scalarVertexKirchhoffSum_crossFaceCoordinate, hzero]
      cases coordinate <;> rfl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ vertex, hboundary⟩
  rcases
      exists_odd_reachable_from_edge_or_cycle_through_edge_of_degree_le_two
        supportEdge hdegree with hroute | hcycle
  · rcases hroute with
      ⟨start, finish, hstart, hfinishOdd, hreachable⟩
    apply Or.inl
    refine ⟨{
      coordinate := coordinate
      coordinate_support := hcoordinate
      start := start
      start_mem_edge := ?_
      finish := finish
      finish_mem_boundarySupport :=
        hoddBoundarySupport finish hfinishOdd
      reachable := hreachable }⟩
    exact hstart
  · rcases hcycle with
      ⟨root, supportCycle, hroot, supportCycleIsCycle, hedgeCycle⟩
    apply Or.inr
    refine ⟨{
      coordinate := coordinate
      coordinate_support := hcoordinate
      root := root
      root_mem_edge := ?_
      supportCycle := supportCycle
      supportCycle_isCycle := supportCycleIsCycle
      edge_mem_supportCycle := ?_ }⟩
    · exact hroot
    · exact hedgeCycle

namespace CompanionCrossPairFusionTargetCollarTraversal

variable {start : sourceNormal.KempeOrbitAdjacentEscape}
  (traversal : CompanionCrossPairFusionTargetCollarTraversal collar start)

/-- The resolved color status of one edge of a rerouted target path.  A
discrepancy is retained only with its charged-interface route or with a
closed support cycle containing the exact contacted common edge. -/
def TargetPathEdgeColorResolution
    (edge : (DeletedAdjacentPairGraph G collar.targetData.firstVertex
      collar.targetData.secondVertex).edgeSet) : Prop :=
  edge ∈ collar.targetEscape.coloring.bicoloredSet
      collar.targetOwnFirstColor collar.targetOwnSecondColor ∨
    ∃ commonEdge : collar.commonCore.edgeSet,
      collar.commonEdgeInTarget commonEdge = edge ∧
        (edge ∈ collar.targetEscape.coloring.bicoloredSet
            (traversal.contact.fusion.lineFusion.normal.returnData.lastOverlap.overlap.fixedColor)
            (traversal.contact.fusion.lineFusion.normal.returnData.lastOverlap.overlap.breakOuterColor) ∨
          edge ∈ collar.targetEscape.coloring.bicoloredSet
            (crossFaceZeroColor
              (traversal.contact.fusion.lineFusion.normal.step.firstHit.transfer.coordinate))
            (traversal.contact.fusion.lineFusion.normal.step.reentry.realization.companion) ∨
          Nonempty (CommonDiscrepancyContactRoute collar
            traversal.contact.fusion.lineFusion.normal.canonicalState
              commonEdge) ∨
          Nonempty (CommonDiscrepancyContactCycle collar
            traversal.contact.fusion.lineFusion.normal.canonicalState
              commonEdge))

/-- Every noncentral collar traversal now has a simple target path whose
every edge has a resolved local color status. -/
theorem exists_targetKempeReroutedPath_with_colorResolution_of_noncentral
    (hclass : traversal.traversalClass = .firstBoundaryPair ∨
      traversal.traversalClass = .secondBoundaryPair ∨
      traversal.traversalClass = .bothBoundaryPairs) :
    ∃ targetPath : (DeletedAdjacentPairGraph G
        collar.targetData.firstVertex collar.targetData.secondVertex).Walk
        ⟨traversal.contact.fusion.startVertex.1,
          traversal.contact.fusion.startVertex_mem_targetRetainedVertexSet⟩
        ⟨traversal.contact.fusion.endVertex.1,
          traversal.contact.fusion.endVertex_mem_targetRetainedVertexSet⟩,
      targetPath.IsPath ∧
        ∀ edge : (DeletedAdjacentPairGraph G collar.targetData.firstVertex
          collar.targetData.secondVertex).edgeSet,
          edge.1 ∈ targetPath.edges →
            traversal.TargetPathEdgeColorResolution edge := by
  rcases
      traversal.exists_targetKempeReroutedPath_with_colorTransport_or_discrepancy_of_noncentral
        hclass with ⟨targetPath, targetPathIsPath, edgeStatus⟩
  refine ⟨targetPath, targetPathIsPath, ?_⟩
  intro edge hedge
  rcases edgeStatus edge hedge with htargetOwn |
      ⟨commonEdge, htargetEdge, hreturn | hselected | hdiscrepancy⟩
  · exact Or.inl htargetOwn
  · exact Or.inr ⟨commonEdge, htargetEdge, Or.inl hreturn⟩
  · exact Or.inr ⟨commonEdge, htargetEdge,
      Or.inr (Or.inl hselected)⟩
  · rcases collar.nonempty_commonDiscrepancyContactRoute_or_cycle
        traversal.contact.fusion.lineFusion.normal.canonicalState
          commonEdge hdiscrepancy with hroute | hcycle
    · exact Or.inr ⟨commonEdge, htargetEdge,
        Or.inr (Or.inr (Or.inl hroute))⟩
    · exact Or.inr ⟨commonEdge, htargetEdge,
        Or.inr (Or.inr (Or.inr hcycle))⟩

/-- Across all seven collar classes, either a target path has fully routed
edgewise color status, or the traversal is one of the four exact central
cross-arm obstructions. -/
theorem exists_targetKempeReroutedPath_with_colorResolution_or_crossObstruction :
    (∃ targetPath : (DeletedAdjacentPairGraph G
        collar.targetData.firstVertex collar.targetData.secondVertex).Walk
        ⟨traversal.contact.fusion.startVertex.1,
          traversal.contact.fusion.startVertex_mem_targetRetainedVertexSet⟩
        ⟨traversal.contact.fusion.endVertex.1,
          traversal.contact.fusion.endVertex_mem_targetRetainedVertexSet⟩,
      targetPath.IsPath ∧
        ∀ edge : (DeletedAdjacentPairGraph G collar.targetData.firstVertex
          collar.targetData.secondVertex).edgeSet,
          edge.1 ∈ targetPath.edges →
            traversal.TargetPathEdgeColorResolution edge) ∨
      ∃ firstUsesOne secondUsesThree,
        traversal.traversalClass = .cross firstUsesOne secondUsesThree ∧
        ¬ collar.targetData.degreeTwoBoundaryData.KempePortsConnected
          collar.targetEscape.coloring collar.targetOwnFirstColor
            collar.targetOwnSecondColor
            (TargetCollarTraversalClass.firstCrossPort firstUsesOne)
            (TargetCollarTraversalClass.secondCrossPort secondUsesThree) := by
  cases hclass : traversal.traversalClass with
  | firstBoundaryPair =>
      exact Or.inl <|
        traversal.exists_targetKempeReroutedPath_with_colorResolution_of_noncentral
          (Or.inl hclass)
  | secondBoundaryPair =>
      exact Or.inl <|
        traversal.exists_targetKempeReroutedPath_with_colorResolution_of_noncentral
          (Or.inr (Or.inl hclass))
  | bothBoundaryPairs =>
      exact Or.inl <|
        traversal.exists_targetKempeReroutedPath_with_colorResolution_of_noncentral
          (Or.inr (Or.inr hclass))
  | cross firstUsesOne secondUsesThree =>
      exact Or.inr ⟨firstUsesOne, secondUsesThree, rfl,
        collar.not_targetOwnKempePortsConnected_cross
          firstUsesOne secondUsesThree⟩

end CompanionCrossPairFusionTargetCollarTraversal

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
