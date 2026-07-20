import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentChangeWitness

set_option autoImplicit false

namespace SimpleGraph.Coloring

universe u v

variable {Vertex : Type u} {Color : Type v}
  {G : SimpleGraph Vertex}

/-- A bicolored walk transports between two colorings whenever the two
colorings agree at every vertex in its support. -/
theorem exists_bicoloredWalk_of_eq_on_support
    (sourceColoring targetColoring : G.Coloring Color)
    (first second : Color)
    {source target : sourceColoring.bicoloredSet first second}
    (path : (sourceColoring.bicoloredSubgraph first second).Walk
      source target)
    (equalOnSupport : ∀ vertex,
      vertex ∈ path.support →
        sourceColoring vertex.1 = targetColoring vertex.1) :
    ∃ (sourceSelected : source.1 ∈
          targetColoring.bicoloredSet first second)
      (targetSelected : target.1 ∈
          targetColoring.bicoloredSet first second),
      Nonempty ((targetColoring.bicoloredSubgraph first second).Walk
        ⟨source.1, sourceSelected⟩ ⟨target.1, targetSelected⟩) := by
  induction path with
  | @nil vertex =>
      have color_eq := equalOnSupport vertex (by simp)
      have selected : vertex.1 ∈
          targetColoring.bicoloredSet first second := by
        rcases vertex.2 with selectedFirst | selectedSecond
        · exact Or.inl (color_eq.symm.trans selectedFirst)
        · exact Or.inr (color_eq.symm.trans selectedSecond)
      exact ⟨selected, selected, ⟨SimpleGraph.Walk.nil⟩⟩
  | @cons firstVertex middleVertex lastVertex adjacent tail ih =>
      have firstColor_eq := equalOnSupport firstVertex (by simp)
      have firstSelected : firstVertex.1 ∈
          targetColoring.bicoloredSet first second := by
        rcases firstVertex.2 with selectedFirst | selectedSecond
        · exact Or.inl (firstColor_eq.symm.trans selectedFirst)
        · exact Or.inr (firstColor_eq.symm.trans selectedSecond)
      have tailEqual : ∀ vertex,
          vertex ∈ tail.support →
            sourceColoring vertex.1 = targetColoring vertex.1 := by
        intro vertex vertex_mem
        exact equalOnSupport vertex (by simp [vertex_mem])
      rcases ih tailEqual with
        ⟨middleSelected, lastSelected, ⟨transportedTail⟩⟩
      have transportedAdjacent :
          (targetColoring.bicoloredSubgraph first second).Adj
            ⟨firstVertex.1, firstSelected⟩
            ⟨middleVertex.1, middleSelected⟩ := by
        exact adjacent
      exact ⟨firstSelected, lastSelected,
        ⟨SimpleGraph.Walk.cons transportedAdjacent transportedTail⟩⟩

/-- If reachability in one bicolored subgraph disappears in a second
coloring which differs only on a set, then the original rooted component
meets that changed set. -/
theorem exists_changedVertex_in_canonicalComponent_of_reachable_not_reachable
    [DecidableEq Color]
    (sourceColoring targetColoring : G.Coloring Color)
    (first second : Color) (changed : Set Vertex)
    (equalOutside : ∀ vertex, vertex ∉ changed →
      sourceColoring vertex = targetColoring vertex)
    (root witness : Vertex)
    (sourceRootSelected : root ∈
      sourceColoring.bicoloredSet first second)
    (sourceWitnessSelected : witness ∈
      sourceColoring.bicoloredSet first second)
    (targetRootSelected : root ∈
      targetColoring.bicoloredSet first second)
    (targetWitnessSelected : witness ∈
      targetColoring.bicoloredSet first second)
    (sourceReachable :
      (sourceColoring.bicoloredSubgraph first second).Reachable
        ⟨root, sourceRootSelected⟩ ⟨witness, sourceWitnessSelected⟩)
    (targetNotReachable :
      ¬(targetColoring.bicoloredSubgraph first second).Reachable
        ⟨root, targetRootSelected⟩ ⟨witness, targetWitnessSelected⟩) :
    ∃ vertex,
      vertex ∈ changed ∧
        vertex ∈ sourceColoring.kempeComponentSetAtVertex
          first second root := by
  rcases sourceReachable with ⟨path⟩
  by_contra noChangedVertex
  push Not at noChangedVertex
  have equalOnSupport : ∀ vertex,
      vertex ∈ path.support →
        sourceColoring vertex.1 = targetColoring vertex.1 := by
    intro vertex vertex_mem
    apply equalOutside vertex.1
    intro vertexChanged
    apply noChangedVertex vertex.1 vertexChanged
    have rootToVertex :
        (sourceColoring.bicoloredSubgraph first second).Reachable
          ⟨root, sourceRootSelected⟩ vertex :=
      (path.takeUntil vertex vertex_mem).reachable
    exact (sourceColoring.mem_kempeComponentSetAtVertex_iff_reachable
      first second root vertex.1 sourceRootSelected vertex.2).2 rootToVertex
  rcases sourceColoring.exists_bicoloredWalk_of_eq_on_support
      targetColoring first second path equalOnSupport with
    ⟨transportedRootSelected, transportedWitnessSelected,
      ⟨transported⟩⟩
  apply targetNotReachable
  simpa only using transported.reachable

end SimpleGraph.Coloring

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
  {start : sourceNormal.KempeOrbitAdjacentEscape}

/-- A component-changing cross-pair step has genuine contact between its
selected Kempe component and one of the two endpoint canonical return
components. -/
structure CompanionCrossPairComponentContact
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  difference : CompanionCanonicalComponentDifference collar start
  contactEdge :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).edgeSet
  contactEdge_mem_selectedComponent : contactEdge ∈
    difference.componentChange.change.changeSource.coloring.kempeComponentSet
      (crossFaceZeroColor difference.step.firstHit.transfer.coordinate)
      difference.step.reentry.realization.companion
      difference.step.reentry.realization.component
  contactEdge_mem_source_or_targetCanonicalComponent :
    contactEdge ∈
        difference.componentChange.returnData.canonicalReturnComponentSet
          difference.componentChange.change.changeSource ∨
      contactEdge ∈
        difference.componentChange.returnData.canonicalReturnComponentSet
          difference.componentChange.change.changeTarget

namespace CompanionCrossPairDirectComponentContact

/-- Direct symmetric-difference contact is, in particular, genuine contact
with one of the two endpoint canonical return components. -/
theorem nonempty_componentContact
    (direct : CompanionCrossPairDirectComponentContact collar start) :
    Nonempty (CompanionCrossPairComponentContact collar start) := by
  rcases
      CompanionCrossPairDirectComponentContact.selectedComponent_meets_source_or_targetCanonicalComponent
        (contact := direct) with
    sourceContact | targetContact
  · exact ⟨{
      difference := direct.difference
      contactEdge := direct.difference.differenceEdge
      contactEdge_mem_selectedComponent := sourceContact.1
      contactEdge_mem_source_or_targetCanonicalComponent :=
        Or.inl sourceContact.2 }⟩
  · exact ⟨{
      difference := direct.difference
      contactEdge := direct.difference.differenceEdge
      contactEdge_mem_selectedComponent := targetContact.1
      contactEdge_mem_source_or_targetCanonicalComponent :=
        Or.inr targetContact.2 }⟩

end CompanionCrossPairDirectComponentContact

namespace CompanionCrossPairRemoteComponentReconnection

variable (reconnection :
  CompanionCrossPairRemoteComponentReconnection collar start)

/-- Away from the selected cross-pair component, the source and target
colorings of a component-changing step agree pointwise. -/
theorem coloring_eq_of_not_mem_selectedComponent
    (edge : (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).edgeSet)
    (edge_not_mem : edge ∉
      reconnection.difference.componentChange.change.changeSource.coloring.kempeComponentSet
        (crossFaceZeroColor
          reconnection.difference.step.firstHit.transfer.coordinate)
        reconnection.difference.step.reentry.realization.companion
        reconnection.difference.step.reentry.realization.component) :
    reconnection.difference.componentChange.change.changeSource.coloring edge =
      reconnection.difference.componentChange.change.changeTarget.coloring edge := by
  rw [← reconnection.difference.successor_eq,
    CompanionAdjacentEscapeStep.successor,
    reconnection.difference.step.reentry.coloring_eq,
    reconnection.difference.componentChange.change.changeSource.coloring
      |>.swapOnKempeComponent_apply_of_not_mem edge_not_mem]

/-- A remote rooted-connectivity flip cannot occur wholly away from the
swapped component: a path existing on one side must enter that component,
thereby producing genuine component contact. -/
theorem nonempty_componentContact
    (reconnection :
      CompanionCrossPairRemoteComponentReconnection collar start) :
    Nonempty (CompanionCrossPairComponentContact collar start) := by
  let sourceColoring :=
    (reconnection.difference.componentChange.change.changeSource).coloring
  let targetColoring :=
    (reconnection.difference.componentChange.change.changeTarget).coloring
  let first :=
    crossFaceZeroColor
      reconnection.difference.step.firstHit.transfer.coordinate
  let second := reconnection.difference.step.reentry.realization.companion
  let component := reconnection.difference.step.reentry.realization.component
  let selectedComponent :=
    sourceColoring.kempeComponentSet first second component
  let fixed :=
    reconnection.difference.componentChange.returnData.lastOverlap.overlap.fixedColor
  let outer :=
    reconnection.difference.componentChange.returnData.lastOverlap.overlap.breakOuterColor
  let root := reconnection.difference.rootEdge
  let witness := reconnection.difference.differenceEdge
  have sourceRootSelected : root ∈
      sourceColoring.bicoloredSet fixed outer :=
    Or.inr reconnection.difference.sourceRootColor_eq_breakOuter
  have targetRootSelected : root ∈
      targetColoring.bicoloredSet fixed outer :=
    Or.inr reconnection.difference.targetRootColor_eq_breakOuter
  have sourceWitnessSelected : witness ∈
      sourceColoring.bicoloredSet fixed outer :=
    reconnection.differenceEdge_selected_in_source_and_target.1
  have targetWitnessSelected : witness ∈
      targetColoring.bicoloredSet fixed outer :=
    reconnection.differenceEdge_selected_in_source_and_target.2
  have equalOutside : ∀ edge, edge ∉ selectedComponent →
      sourceColoring edge = targetColoring edge := by
    intro edge edge_not_mem
    exact reconnection.coloring_eq_of_not_mem_selectedComponent edge
      edge_not_mem
  have reachabilityFlip :=
    reconnection.sourceReachable_not_targetReachable_or_reverse
  dsimp only at reachabilityFlip
  rcases reachabilityFlip with sourceToTarget | targetToSource
  · rcases sourceColoring
        |>.exists_changedVertex_in_canonicalComponent_of_reachable_not_reachable
          targetColoring fixed outer selectedComponent equalOutside root witness
          sourceRootSelected sourceWitnessSelected targetRootSelected
          targetWitnessSelected sourceToTarget.1 sourceToTarget.2 with
      ⟨contactEdge, contactEdgeSelected, contactEdgeCanonical⟩
    exact ⟨{
      difference := reconnection.difference
      contactEdge := contactEdge
      contactEdge_mem_selectedComponent := contactEdgeSelected
      contactEdge_mem_source_or_targetCanonicalComponent :=
        Or.inl contactEdgeCanonical }⟩
  · rcases targetColoring
        |>.exists_changedVertex_in_canonicalComponent_of_reachable_not_reachable
          sourceColoring fixed outer selectedComponent
          (fun edge edge_not_mem => (equalOutside edge edge_not_mem).symm)
          root witness targetRootSelected targetWitnessSelected
          sourceRootSelected sourceWitnessSelected targetToSource.2
          targetToSource.1 with
      ⟨contactEdge, contactEdgeSelected, contactEdgeCanonical⟩
    exact ⟨{
      difference := reconnection.difference
      contactEdge := contactEdge
      contactEdge_mem_selectedComponent := contactEdgeSelected
      contactEdge_mem_source_or_targetCanonicalComponent :=
        Or.inr contactEdgeCanonical }⟩

end CompanionCrossPairRemoteComponentReconnection

/-- Every canonical component change is witnessed by genuine contact between
the selected cross-pair component and an endpoint canonical return component. -/
theorem CompanionCanonicalSamePairComponentChange.nonempty_componentContact
    (componentChange :
      CompanionCanonicalSamePairComponentChange collar start) :
    Nonempty (CompanionCrossPairComponentContact collar start) := by
  rcases componentChange.directContact_or_remoteReconnection with
    direct | remote
  · rcases direct with ⟨direct⟩
    exact CompanionCrossPairDirectComponentContact.nonempty_componentContact
      (direct := direct)
  · rcases remote with ⟨remote⟩
    exact CompanionCrossPairRemoteComponentReconnection.nonempty_componentContact
      (reconnection := remote)

/-- A closed companion circuit resolves into local cancellation, a retained
cross-pair intersection, genuine component contact, a shared-edge pivot, or
full three-pair monodromy.  No opaque remote-reconnection branch remains. -/
theorem closedCircuit_exists_localCancellation_or_crossPairIntersection_or_componentContact_or_edgePivot_or_threePairMonodromy
    (closed : Relation.TransGen
      (CompanionAdjacentEscapeTransition collar) start start) :
    Nonempty (CompanionCanonicalComponentDisjointClosure collar start) ∨
      Nonempty (CompanionCanonicalComponentIntersection collar start) ∨
        Nonempty (CompanionCrossPairComponentContact collar start) ∨
          Nonempty (CompanionSameOuterTargetAvoidingEdgePivot collar start) ∨
            Nonempty (CompanionThreePairMonodromy collar start) := by
  rcases
      closedCircuit_exists_localCancellation_or_crossPairIntersection_or_componentChange_or_edgePivot_or_threePairMonodromy
        closed with hcancel | hintersection | hchange | hpivot | hmonodromy
  · exact Or.inl hcancel
  · exact Or.inr (Or.inl hintersection)
  · rcases hchange with ⟨componentChange⟩
    exact Or.inr (Or.inr (Or.inl componentChange.nonempty_componentContact))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpivot)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hmonodromy)))

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
