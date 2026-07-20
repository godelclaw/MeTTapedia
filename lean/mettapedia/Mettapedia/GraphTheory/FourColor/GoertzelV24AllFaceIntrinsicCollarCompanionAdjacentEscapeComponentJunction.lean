import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentIntersection

set_option autoImplicit false

namespace SimpleGraph.Coloring

universe u v

variable {Vertex : Type u} {Color : Type v}
  {G : SimpleGraph Vertex}

/-- Two vertices in the same selected Kempe component are joined by a
simple path in the corresponding bicolored subgraph. -/
theorem exists_bicoloredPath_of_mem_kempeComponentSet
    (coloring : G.Coloring Color) (first second : Color)
    (component :
      (coloring.bicoloredSubgraph first second).ConnectedComponent)
    {source target : Vertex}
    (source_mem : source ∈
      coloring.kempeComponentSet first second component)
    (target_mem : target ∈
      coloring.kempeComponentSet first second component) :
    ∃ (sourceSelected : source ∈
          coloring.bicoloredSet first second)
      (targetSelected : target ∈
          coloring.bicoloredSet first second)
      (path : (coloring.bicoloredSubgraph first second).Walk
        ⟨source, sourceSelected⟩ ⟨target, targetSelected⟩),
      path.IsPath := by
  rcases source_mem with ⟨sourceSelected, sourceComponent⟩
  rcases target_mem with ⟨targetSelected, targetComponent⟩
  have reachable : (coloring.bicoloredSubgraph first second).Reachable
      ⟨source, sourceSelected⟩ ⟨target, targetSelected⟩ :=
    SimpleGraph.ConnectedComponent.eq.mp
      (sourceComponent.trans targetComponent.symm)
  rcases reachable.exists_isPath with ⟨path, isPath⟩
  exact ⟨sourceSelected, targetSelected, path, isPath⟩

/-- Membership in a canonical rooted component always implies membership
in the selected two-color vertex set. -/
theorem mem_bicoloredSet_of_mem_kempeComponentSetAtVertex
    [DecidableEq Color] (coloring : G.Coloring Color)
    (first second : Color) (root : Vertex) {vertex : Vertex}
    (member : vertex ∈
      coloring.kempeComponentSetAtVertex first second root) :
    vertex ∈ coloring.bicoloredSet first second := by
  by_cases rootSelected : root ∈ coloring.bicoloredSet first second
  · rw [coloring.kempeComponentSetAtVertex_eq_of_mem
      first second root rootSelected] at member
    exact coloring.mem_bicoloredSet_of_mem_kempeComponentSet member
  · have rootValue :
        ¬(coloring root = first ∨ coloring root = second) := rootSelected
    unfold kempeComponentSetAtVertex at member
    rw [dif_neg rootValue] at member
    exact False.elim member

/-- With selected endpoints, membership in the canonical rooted component
is exactly bicolored reachability from the root. -/
theorem mem_kempeComponentSetAtVertex_iff_reachable
    [DecidableEq Color] (coloring : G.Coloring Color)
    (first second : Color) (root vertex : Vertex)
    (rootSelected : root ∈ coloring.bicoloredSet first second)
    (vertexSelected : vertex ∈ coloring.bicoloredSet first second) :
    vertex ∈ coloring.kempeComponentSetAtVertex first second root ↔
      (coloring.bicoloredSubgraph first second).Reachable
        ⟨root, rootSelected⟩ ⟨vertex, vertexSelected⟩ := by
  rw [coloring.kempeComponentSetAtVertex_eq_of_mem
    first second root rootSelected]
  constructor
  · rintro ⟨selected, component_eq⟩
    have vertex_eq :
        (⟨vertex, selected⟩ : coloring.bicoloredSet first second) =
          ⟨vertex, vertexSelected⟩ := rfl
    have reachable := SimpleGraph.ConnectedComponent.eq.mp component_eq
    simpa only [vertex_eq] using reachable.symm
  · intro reachable
    exact ⟨vertexSelected,
      (SimpleGraph.ConnectedComponent.sound reachable).symm⟩

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

namespace CompanionCanonicalComponentIntersection

variable (intersection : CompanionCanonicalComponentIntersection collar start)

/-- The lifted common-core edge rooting the return-pair component. -/
def rootEdge :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).edgeSet :=
  collar.commonEdgeInSource
    intersection.closure.returnData.lastOverlap.overlap.commonEdge

/-- A canonical support edge certifying where the intersecting recursive
step was launched. -/
noncomputable def launchSupportEdge :
    intersection.step.firstHit.transfer.SupportEdge :=
  intersection.step.firstHit.transfer.supportEdgeWord.head
    intersection.step.firstHit.transfer.supportEdgeWord_ne_nil

/-- The source-deletion image of the canonical launch support edge. -/
noncomputable def launchEdge :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).edgeSet :=
  collar.commonEdgeInSource intersection.launchSupportEdge.1

/-- The canonical launch edge belongs to the actual selected component of
the intersecting transition. -/
theorem launchEdge_mem_selectedComponent : intersection.launchEdge ∈
    intersection.intersectionSource.coloring.kempeComponentSet
      (crossFaceZeroColor intersection.step.firstHit.transfer.coordinate)
      intersection.step.reentry.realization.companion
      intersection.step.reentry.realization.component := by
  apply intersection.step.reentry.realization.support_mem_component
    intersection.launchSupportEdge
  exact List.head_mem
    intersection.step.firstHit.transfer.supportEdgeWord_ne_nil

/-- The intersection occurs away from the shared root edge. -/
theorem rootEdge_ne_intersectionEdge :
    intersection.rootEdge ≠ intersection.intersectionEdge := by
  intro edge_eq
  apply intersection.root_not_mem_selectedComponent
  change intersection.rootEdge ∈
    intersection.intersectionSource.coloring.kempeComponentSet
      (crossFaceZeroColor intersection.step.firstHit.transfer.coordinate)
      intersection.step.reentry.realization.companion
      intersection.step.reentry.realization.component
  rw [edge_eq]
  exact intersection.intersectionEdge_mem_selected

/-- The canonical return component supplies a nontrivial simple bicolored
path from the shared root edge to the retained intersection edge. -/
theorem exists_returnPath_to_intersection :
    ∃ (rootSelected : intersection.rootEdge ∈
          intersection.intersectionSource.coloring.bicoloredSet
            intersection.closure.returnData.lastOverlap.overlap.fixedColor
            intersection.closure.returnData.lastOverlap.overlap.breakOuterColor)
      (intersectionSelected : intersection.intersectionEdge ∈
          intersection.intersectionSource.coloring.bicoloredSet
            intersection.closure.returnData.lastOverlap.overlap.fixedColor
            intersection.closure.returnData.lastOverlap.overlap.breakOuterColor)
      (path : (intersection.intersectionSource.coloring.bicoloredSubgraph
          intersection.closure.returnData.lastOverlap.overlap.fixedColor
          intersection.closure.returnData.lastOverlap.overlap.breakOuterColor).Walk
        ⟨intersection.rootEdge, rootSelected⟩
        ⟨intersection.intersectionEdge, intersectionSelected⟩),
      path.IsPath ∧ 0 < path.length := by
  let coloring := intersection.intersectionSource.coloring
  let fixed := intersection.closure.returnData.lastOverlap.overlap.fixedColor
  let outer :=
    intersection.closure.returnData.lastOverlap.overlap.breakOuterColor
  have rootSelected : intersection.rootEdge ∈
      coloring.bicoloredSet fixed outer := by
    exact Or.inr intersection.rootColor_eq_breakOuter
  have root_mem : intersection.rootEdge ∈
      coloring.kempeComponentSet fixed outer
        ((coloring.bicoloredSubgraph fixed outer).connectedComponentMk
          ⟨intersection.rootEdge, rootSelected⟩) :=
    coloring.mem_kempeComponentSet_self rootSelected
  have intersection_mem : intersection.intersectionEdge ∈
      coloring.kempeComponentSet fixed outer
        ((coloring.bicoloredSubgraph fixed outer).connectedComponentMk
          ⟨intersection.rootEdge, rootSelected⟩) := by
    have retained := intersection.intersectionEdge_mem_canonical
    change intersection.intersectionEdge ∈
      coloring.kempeComponentSetAtVertex fixed outer
        intersection.rootEdge at retained
    rw [coloring.kempeComponentSetAtVertex_eq_of_mem
      fixed outer intersection.rootEdge rootSelected] at retained
    exact retained
  rcases coloring.exists_bicoloredPath_of_mem_kempeComponentSet
      fixed outer _ root_mem intersection_mem with
    ⟨rootSelected', intersectionSelected, path, isPath⟩
  have endpoints_ne :
      (⟨intersection.rootEdge, rootSelected'⟩ :
          coloring.bicoloredSet fixed outer) ≠
        ⟨intersection.intersectionEdge, intersectionSelected⟩ := by
    intro endpoints_eq
    exact intersection.rootEdge_ne_intersectionEdge
      (congrArg Subtype.val endpoints_eq)
  exact ⟨rootSelected', intersectionSelected, path, isPath,
    SimpleGraph.Walk.not_nil_iff_lt_length.mp
      (SimpleGraph.Walk.not_nil_of_ne endpoints_ne)⟩

/-- The actual cross-pair component supplies a simple bicolored path from
the certified launch support to the retained intersection. -/
theorem exists_selectedPath_to_intersection :
    ∃ (launchSelected : intersection.launchEdge ∈
          intersection.intersectionSource.coloring.bicoloredSet
            (crossFaceZeroColor
              intersection.step.firstHit.transfer.coordinate)
            intersection.step.reentry.realization.companion)
      (intersectionSelected : intersection.intersectionEdge ∈
          intersection.intersectionSource.coloring.bicoloredSet
            (crossFaceZeroColor
              intersection.step.firstHit.transfer.coordinate)
            intersection.step.reentry.realization.companion)
      (path : (intersection.intersectionSource.coloring.bicoloredSubgraph
          (crossFaceZeroColor
            intersection.step.firstHit.transfer.coordinate)
          intersection.step.reentry.realization.companion).Walk
        ⟨intersection.launchEdge, launchSelected⟩
        ⟨intersection.intersectionEdge, intersectionSelected⟩),
      path.IsPath := by
  exact intersection.intersectionSource.coloring
    |>.exists_bicoloredPath_of_mem_kempeComponentSet
      (crossFaceZeroColor intersection.step.firstHit.transfer.coordinate)
      intersection.step.reentry.realization.companion
      intersection.step.reentry.realization.component
      intersection.launchEdge_mem_selectedComponent
      intersection.intersectionEdge_mem_selected

/-- At the retained junction, the cross-pair classification also fixes the
edge color: fixed in the fixed/third branch and outer in the outer/third
branch. -/
theorem selectedPair_and_intersectionColor_classification :
    (({crossFaceZeroColor intersection.step.firstHit.transfer.coordinate,
          intersection.step.reentry.realization.companion} : Set Color) =
        {intersection.closure.returnData.lastOverlap.overlap.fixedColor,
          intersection.closure.returnData.lastOverlap.overlap.fixedColor +
            intersection.closure.returnData.lastOverlap.overlap.breakOuterColor} ∧
      intersection.intersectionSource.coloring intersection.intersectionEdge =
        intersection.closure.returnData.lastOverlap.overlap.fixedColor) ∨
      (({crossFaceZeroColor intersection.step.firstHit.transfer.coordinate,
          intersection.step.reentry.realization.companion} : Set Color) =
        {intersection.closure.returnData.lastOverlap.overlap.breakOuterColor,
          intersection.closure.returnData.lastOverlap.overlap.fixedColor +
            intersection.closure.returnData.lastOverlap.overlap.breakOuterColor} ∧
      intersection.intersectionSource.coloring intersection.intersectionEdge =
        intersection.closure.returnData.lastOverlap.overlap.breakOuterColor) := by
  let coloring := intersection.intersectionSource.coloring
  let first :=
    crossFaceZeroColor intersection.step.firstHit.transfer.coordinate
  let second := intersection.step.reentry.realization.companion
  let fixed := intersection.closure.returnData.lastOverlap.overlap.fixedColor
  let outer :=
    intersection.closure.returnData.lastOverlap.overlap.breakOuterColor
  let third := fixed + outer
  have returnSelected : intersection.intersectionEdge ∈
      coloring.bicoloredSet fixed outer := by
    have rootSelected : intersection.rootEdge ∈
        coloring.bicoloredSet fixed outer :=
      Or.inr intersection.rootColor_eq_breakOuter
    have retained := intersection.intersectionEdge_mem_canonical
    change intersection.intersectionEdge ∈
      coloring.kempeComponentSetAtVertex fixed outer
        intersection.rootEdge at retained
    rw [coloring.kempeComponentSetAtVertex_eq_of_mem
      fixed outer intersection.rootEdge rootSelected] at retained
    exact coloring.mem_bicoloredSet_of_mem_kempeComponentSet retained
  have selectedValue : coloring intersection.intersectionEdge ∈
      ({first, second} : Set Color) := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
      first, second, coloring] using
      coloring.mem_bicoloredSet_of_mem_kempeComponentSet
        intersection.intersectionEdge_mem_selected
  rcases intersection.selectedPair_classification with
    fixedThird | outerThird
  · apply Or.inl
    refine ⟨fixedThird, ?_⟩
    have crossSelected : intersection.intersectionEdge ∈
        coloring.bicoloredSet fixed third := by
      rw [fixedThird] at selectedValue
      change coloring intersection.intersectionEdge = fixed ∨
        coloring intersection.intersectionEdge = third
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
        third, fixed, outer] using selectedValue
    exact coloring.color_eq_of_mem_two_bicoloredSets
      (Ne.symm (add_ne_right_of_ne_zero
        intersection.closure.returnData.lastOverlap.overlap.fixedColor_ne_zero))
      returnSelected crossSelected
  · apply Or.inr
    refine ⟨outerThird, ?_⟩
    have crossSelected : intersection.intersectionEdge ∈
        coloring.bicoloredSet outer third := by
      rw [outerThird] at selectedValue
      change coloring intersection.intersectionEdge = outer ∨
        coloring intersection.intersectionEdge = third
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
        third, fixed, outer] using selectedValue
    have returnSelected' : intersection.intersectionEdge ∈
        coloring.bicoloredSet outer fixed :=
      returnSelected.elim Or.inr Or.inl
    exact coloring.color_eq_of_mem_two_bicoloredSets
      (Ne.symm (add_ne_left_of_ne_zero
        intersection.closure.returnData.lastOverlap.overlap.breakOuterColor_ne_zero))
      returnSelected' crossSelected

end CompanionCanonicalComponentIntersection

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
