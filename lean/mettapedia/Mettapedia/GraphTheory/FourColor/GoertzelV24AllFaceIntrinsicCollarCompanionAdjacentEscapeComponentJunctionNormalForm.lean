import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentContact

set_option autoImplicit false

namespace SimpleGraph.Coloring

universe u v

variable {Vertex : Type u} {Color : Type v}
  {G : SimpleGraph Vertex}

/-- A bicolored walk transports to any coloring in which every vertex of
its support remains selected by the same two colors. -/
theorem exists_bicoloredWalk_of_selected_support
    (sourceColoring targetColoring : G.Coloring Color)
    (first second : Color)
    {source target : sourceColoring.bicoloredSet first second}
    (walk : (sourceColoring.bicoloredSubgraph first second).Walk
      source target)
    (selectedOnSupport : ∀ vertex,
      vertex ∈ walk.support →
        vertex.1 ∈ targetColoring.bicoloredSet first second) :
    ∃ (sourceSelected : source.1 ∈
          targetColoring.bicoloredSet first second)
      (targetSelected : target.1 ∈
          targetColoring.bicoloredSet first second),
      Nonempty ((targetColoring.bicoloredSubgraph first second).Walk
        ⟨source.1, sourceSelected⟩ ⟨target.1, targetSelected⟩) := by
  induction walk with
  | @nil vertex =>
      have selected := selectedOnSupport vertex (by simp)
      exact ⟨selected, selected, ⟨SimpleGraph.Walk.nil⟩⟩
  | @cons firstVertex middleVertex lastVertex adjacent tail ih =>
      have firstSelected := selectedOnSupport firstVertex (by simp)
      have tailSelected : ∀ vertex,
          vertex ∈ tail.support →
            vertex.1 ∈ targetColoring.bicoloredSet first second := by
        intro vertex vertex_mem
        exact selectedOnSupport vertex (by simp [vertex_mem])
      rcases ih tailSelected with
        ⟨middleSelected, lastSelected, ⟨transportedTail⟩⟩
      have transportedAdjacent :
          (targetColoring.bicoloredSubgraph first second).Adj
            ⟨firstVertex.1, firstSelected⟩
            ⟨middleVertex.1, middleSelected⟩ := by
        exact adjacent
      exact ⟨firstSelected, lastSelected,
        ⟨SimpleGraph.Walk.cons transportedAdjacent transportedTail⟩⟩

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

namespace CompanionCanonicalComponentDifference

variable (difference : CompanionCanonicalComponentDifference collar start)

/-- The target coloring of a component-changing step is exactly the source
coloring with the classified cross-pair component swapped. -/
theorem targetColoring_eq_swap :
    difference.componentChange.change.changeTarget.coloring =
      difference.componentChange.change.changeSource.coloring.swapOnKempeComponent
        (crossFaceZeroColor difference.step.firstHit.transfer.coordinate)
        difference.step.reentry.realization.companion
        difference.step.reentry.realization.component := by
  calc
    difference.componentChange.change.changeTarget.coloring =
        difference.step.successor.coloring :=
      congrArg (fun escape => escape.coloring) difference.successor_eq.symm
    _ = difference.step.reentry.realization.coloring := by
      simpa only [CompanionAdjacentEscapeStep.successor] using
        difference.step.reentry.coloring_eq
    _ = difference.componentChange.change.changeSource.coloring.swapOnKempeComponent
          (crossFaceZeroColor difference.step.firstHit.transfer.coordinate)
          difference.step.reentry.realization.companion
          difference.step.reentry.realization.component := rfl

end CompanionCanonicalComponentDifference

/-- Uniform local data at either a retained component intersection or a
component-changing contact.  Both Kempe paths live in `canonicalState`:
the return path by definition, and the selected path via exact preservation
of its two-color support. -/
structure CompanionCrossPairJunctionNormalForm
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  returnData : CompanionSameOuterEdgeConstantReturn collar start
  sourceState : sourceNormal.KempeOrbitAdjacentEscape
  canonicalState : sourceNormal.KempeOrbitAdjacentEscape
  step : CompanionAdjacentEscapeStep collar sourceState
  rootColor_eq_breakOuter :
    canonicalState.coloring
        (collar.commonEdgeInSource
          returnData.lastOverlap.overlap.commonEdge) =
      returnData.lastOverlap.overlap.breakOuterColor
  root_not_mem_selectedComponent :
    collar.commonEdgeInSource
          returnData.lastOverlap.overlap.commonEdge ∉
      sourceState.coloring.kempeComponentSet
        (crossFaceZeroColor step.firstHit.transfer.coordinate)
        step.reentry.realization.companion
        step.reentry.realization.component
  junctionEdge :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).edgeSet
  junctionEdge_mem_selectedComponent : junctionEdge ∈
    sourceState.coloring.kempeComponentSet
      (crossFaceZeroColor step.firstHit.transfer.coordinate)
      step.reentry.realization.companion
      step.reentry.realization.component
  junctionEdge_mem_canonicalComponent : junctionEdge ∈
    returnData.canonicalReturnComponentSet canonicalState
  selectedSupportTransport : ∀ edge,
    edge ∈ sourceState.coloring.bicoloredSet
        (crossFaceZeroColor step.firstHit.transfer.coordinate)
        step.reentry.realization.companion →
      edge ∈ canonicalState.coloring.bicoloredSet
        (crossFaceZeroColor step.firstHit.transfer.coordinate)
        step.reentry.realization.companion
  pairClassification :
    (({crossFaceZeroColor step.firstHit.transfer.coordinate,
          step.reentry.realization.companion} : Set Color) =
        {returnData.lastOverlap.overlap.fixedColor,
          returnData.lastOverlap.overlap.fixedColor +
            returnData.lastOverlap.overlap.breakOuterColor} ∨
      ({crossFaceZeroColor step.firstHit.transfer.coordinate,
          step.reentry.realization.companion} : Set Color) =
        {returnData.lastOverlap.overlap.breakOuterColor,
          returnData.lastOverlap.overlap.fixedColor +
            returnData.lastOverlap.overlap.breakOuterColor})

namespace CompanionCanonicalComponentIntersection

variable (intersection : CompanionCanonicalComponentIntersection collar start)

/-- A retained same-component intersection is already a junction normal
form, with source and canonical states equal. -/
def toCrossPairJunctionNormalForm :
    CompanionCrossPairJunctionNormalForm collar start := {
  returnData := intersection.closure.returnData
  sourceState := intersection.intersectionSource
  canonicalState := intersection.intersectionSource
  step := intersection.step
  rootColor_eq_breakOuter := intersection.rootColor_eq_breakOuter
  root_not_mem_selectedComponent := intersection.root_not_mem_selectedComponent
  junctionEdge := intersection.intersectionEdge
  junctionEdge_mem_selectedComponent :=
    intersection.intersectionEdge_mem_selected
  junctionEdge_mem_canonicalComponent :=
    intersection.intersectionEdge_mem_canonical
  selectedSupportTransport := fun _ member => member
  pairClassification := intersection.selectedPair_classification }

end CompanionCanonicalComponentIntersection

namespace CompanionCrossPairComponentContact

/-- A component-changing contact admits the same junction normal form.
If contact is recorded in the target canonical component, invariance of the
selected two-color support transports the selected path across the swap. -/
theorem nonempty_crossPairJunctionNormalForm
    (contact : CompanionCrossPairComponentContact collar start) :
    Nonempty (CompanionCrossPairJunctionNormalForm collar start) := by
  let difference := contact.difference
  let sourceState := difference.componentChange.change.changeSource
  let targetState := difference.componentChange.change.changeTarget
  let first := crossFaceZeroColor difference.step.firstHit.transfer.coordinate
  let second := difference.step.reentry.realization.companion
  let component := difference.step.reentry.realization.component
  rcases contact.contactEdge_mem_source_or_targetCanonicalComponent with
    sourceContact | targetContact
  · exact ⟨{
      returnData := difference.componentChange.returnData
      sourceState := sourceState
      canonicalState := sourceState
      step := difference.step
      rootColor_eq_breakOuter := difference.sourceRootColor_eq_breakOuter
      root_not_mem_selectedComponent :=
        difference.root_not_mem_selectedComponent
      junctionEdge := contact.contactEdge
      junctionEdge_mem_selectedComponent :=
        contact.contactEdge_mem_selectedComponent
      junctionEdge_mem_canonicalComponent := sourceContact
      selectedSupportTransport := fun _ member => member
      pairClassification := difference.pairClassification }⟩
  · have supportTransport : ∀ edge,
        edge ∈ sourceState.coloring.bicoloredSet first second →
          edge ∈ targetState.coloring.bicoloredSet first second := by
      intro edge member
      rw [difference.targetColoring_eq_swap]
      exact (sourceState.coloring
        |>.mem_bicoloredSet_swapOnKempeComponent_iff
          first second component edge).2 member
    exact ⟨{
      returnData := difference.componentChange.returnData
      sourceState := sourceState
      canonicalState := targetState
      step := difference.step
      rootColor_eq_breakOuter := difference.targetRootColor_eq_breakOuter
      root_not_mem_selectedComponent :=
        difference.root_not_mem_selectedComponent
      junctionEdge := contact.contactEdge
      junctionEdge_mem_selectedComponent :=
        contact.contactEdge_mem_selectedComponent
      junctionEdge_mem_canonicalComponent := targetContact
      selectedSupportTransport := supportTransport
      pairClassification := difference.pairClassification }⟩

end CompanionCrossPairComponentContact

namespace CompanionCrossPairJunctionNormalForm

variable (normal : CompanionCrossPairJunctionNormalForm collar start)

/-- The fixed common-core edge rooting the return component. -/
def rootEdge :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).edgeSet :=
  collar.commonEdgeInSource normal.returnData.lastOverlap.overlap.commonEdge

/-- A canonical support edge certifying the selected component's launch. -/
noncomputable def launchSupportEdge :
    normal.step.firstHit.transfer.SupportEdge :=
  normal.step.firstHit.transfer.supportEdgeWord.head
    normal.step.firstHit.transfer.supportEdgeWord_ne_nil

/-- The launch support edge in the source deleted-pair graph. -/
noncomputable def launchEdge :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).edgeSet :=
  collar.commonEdgeInSource normal.launchSupportEdge.1

/-- The canonical launch edge lies in the selected component. -/
theorem launchEdge_mem_selectedComponent : normal.launchEdge ∈
    normal.sourceState.coloring.kempeComponentSet
      (crossFaceZeroColor normal.step.firstHit.transfer.coordinate)
      normal.step.reentry.realization.companion
      normal.step.reentry.realization.component := by
  apply normal.step.reentry.realization.support_mem_component
    normal.launchSupportEdge
  exact List.head_mem normal.step.firstHit.transfer.supportEdgeWord_ne_nil

/-- A junction never coincides with the return root, which the selected
cross-pair component avoids. -/
theorem rootEdge_ne_junctionEdge :
    normal.rootEdge ≠ normal.junctionEdge := by
  intro edge_eq
  apply normal.root_not_mem_selectedComponent
  change normal.rootEdge ∈
    normal.sourceState.coloring.kempeComponentSet
      (crossFaceZeroColor normal.step.firstHit.transfer.coordinate)
      normal.step.reentry.realization.companion
      normal.step.reentry.realization.component
  rw [edge_eq]
  exact normal.junctionEdge_mem_selectedComponent

/-- The canonical return component supplies a positive simple path from
the common root to the junction. -/
theorem exists_returnPath_to_junction :
    ∃ (rootSelected : normal.rootEdge ∈
          normal.canonicalState.coloring.bicoloredSet
            normal.returnData.lastOverlap.overlap.fixedColor
            normal.returnData.lastOverlap.overlap.breakOuterColor)
      (junctionSelected : normal.junctionEdge ∈
          normal.canonicalState.coloring.bicoloredSet
            normal.returnData.lastOverlap.overlap.fixedColor
            normal.returnData.lastOverlap.overlap.breakOuterColor)
      (path : (normal.canonicalState.coloring.bicoloredSubgraph
          normal.returnData.lastOverlap.overlap.fixedColor
          normal.returnData.lastOverlap.overlap.breakOuterColor).Walk
        ⟨normal.rootEdge, rootSelected⟩
        ⟨normal.junctionEdge, junctionSelected⟩),
      path.IsPath ∧ 0 < path.length := by
  let coloring := normal.canonicalState.coloring
  let fixed := normal.returnData.lastOverlap.overlap.fixedColor
  let outer := normal.returnData.lastOverlap.overlap.breakOuterColor
  have rootSelected : normal.rootEdge ∈
      coloring.bicoloredSet fixed outer :=
    Or.inr normal.rootColor_eq_breakOuter
  have root_mem : normal.rootEdge ∈
      coloring.kempeComponentSet fixed outer
        ((coloring.bicoloredSubgraph fixed outer).connectedComponentMk
          ⟨normal.rootEdge, rootSelected⟩) :=
    coloring.mem_kempeComponentSet_self rootSelected
  have junction_mem : normal.junctionEdge ∈
      coloring.kempeComponentSet fixed outer
        ((coloring.bicoloredSubgraph fixed outer).connectedComponentMk
          ⟨normal.rootEdge, rootSelected⟩) := by
    have retained := normal.junctionEdge_mem_canonicalComponent
    change normal.junctionEdge ∈
      coloring.kempeComponentSetAtVertex fixed outer normal.rootEdge at retained
    rw [coloring.kempeComponentSetAtVertex_eq_of_mem
      fixed outer normal.rootEdge rootSelected] at retained
    exact retained
  rcases coloring.exists_bicoloredPath_of_mem_kempeComponentSet
      fixed outer _ root_mem junction_mem with
    ⟨rootSelected', junctionSelected, path, isPath⟩
  have endpoints_ne :
      (⟨normal.rootEdge, rootSelected'⟩ : coloring.bicoloredSet fixed outer) ≠
        ⟨normal.junctionEdge, junctionSelected⟩ := by
    intro endpoints_eq
    exact normal.rootEdge_ne_junctionEdge
      (congrArg Subtype.val endpoints_eq)
  exact ⟨rootSelected', junctionSelected, path, isPath,
    SimpleGraph.Walk.not_nil_iff_lt_length.mp
      (SimpleGraph.Walk.not_nil_of_ne endpoints_ne)⟩

/-- After selected-support transport, the actual cross-pair component
supplies a simple path from its certified launch edge to the junction in the
same coloring as the canonical return path. -/
theorem exists_selectedPath_to_junction :
    ∃ (launchSelected : normal.launchEdge ∈
          normal.canonicalState.coloring.bicoloredSet
            (crossFaceZeroColor normal.step.firstHit.transfer.coordinate)
            normal.step.reentry.realization.companion)
      (junctionSelected : normal.junctionEdge ∈
          normal.canonicalState.coloring.bicoloredSet
            (crossFaceZeroColor normal.step.firstHit.transfer.coordinate)
            normal.step.reentry.realization.companion)
      (path : (normal.canonicalState.coloring.bicoloredSubgraph
          (crossFaceZeroColor normal.step.firstHit.transfer.coordinate)
          normal.step.reentry.realization.companion).Walk
        ⟨normal.launchEdge, launchSelected⟩
        ⟨normal.junctionEdge, junctionSelected⟩),
      path.IsPath := by
  let sourceColoring := normal.sourceState.coloring
  let canonicalColoring := normal.canonicalState.coloring
  let first := crossFaceZeroColor normal.step.firstHit.transfer.coordinate
  let second := normal.step.reentry.realization.companion
  rcases sourceColoring.exists_bicoloredPath_of_mem_kempeComponentSet
      first second normal.step.reentry.realization.component
      normal.launchEdge_mem_selectedComponent
      normal.junctionEdge_mem_selectedComponent with
    ⟨launchSelected, junctionSelected, sourcePath, _sourceIsPath⟩
  have selectedOnSupport : ∀ vertex,
      vertex ∈ sourcePath.support →
        vertex.1 ∈ canonicalColoring.bicoloredSet first second := by
    intro vertex _vertex_mem
    exact normal.selectedSupportTransport vertex.1 vertex.2
  rcases sourceColoring.exists_bicoloredWalk_of_selected_support
      canonicalColoring first second sourcePath selectedOnSupport with
    ⟨canonicalLaunchSelected, canonicalJunctionSelected,
      ⟨transported⟩⟩
  rcases transported.reachable.exists_isPath with ⟨path, isPath⟩
  exact ⟨canonicalLaunchSelected, canonicalJunctionSelected, path, isPath⟩

/-- At a normalized junction the shared edge has the common selected color:
fixed in the fixed/third branch, or outer in the outer/third branch. -/
theorem selectedPair_and_junctionColor_classification :
    (({crossFaceZeroColor normal.step.firstHit.transfer.coordinate,
          normal.step.reentry.realization.companion} : Set Color) =
        {normal.returnData.lastOverlap.overlap.fixedColor,
          normal.returnData.lastOverlap.overlap.fixedColor +
            normal.returnData.lastOverlap.overlap.breakOuterColor} ∧
      normal.canonicalState.coloring normal.junctionEdge =
        normal.returnData.lastOverlap.overlap.fixedColor) ∨
      (({crossFaceZeroColor normal.step.firstHit.transfer.coordinate,
          normal.step.reentry.realization.companion} : Set Color) =
        {normal.returnData.lastOverlap.overlap.breakOuterColor,
          normal.returnData.lastOverlap.overlap.fixedColor +
            normal.returnData.lastOverlap.overlap.breakOuterColor} ∧
      normal.canonicalState.coloring normal.junctionEdge =
        normal.returnData.lastOverlap.overlap.breakOuterColor) := by
  let coloring := normal.canonicalState.coloring
  let sourceColoring := normal.sourceState.coloring
  let first := crossFaceZeroColor normal.step.firstHit.transfer.coordinate
  let second := normal.step.reentry.realization.companion
  let fixed := normal.returnData.lastOverlap.overlap.fixedColor
  let outer := normal.returnData.lastOverlap.overlap.breakOuterColor
  let third := fixed + outer
  have returnSelected : normal.junctionEdge ∈
      coloring.bicoloredSet fixed outer := by
    exact coloring.mem_bicoloredSet_of_mem_kempeComponentSetAtVertex
      fixed outer normal.rootEdge normal.junctionEdge_mem_canonicalComponent
  have sourceCrossSelected : normal.junctionEdge ∈
      sourceColoring.bicoloredSet first second :=
    sourceColoring.mem_bicoloredSet_of_mem_kempeComponentSet
      normal.junctionEdge_mem_selectedComponent
  have crossSelected : normal.junctionEdge ∈
      coloring.bicoloredSet first second :=
    normal.selectedSupportTransport normal.junctionEdge sourceCrossSelected
  change coloring normal.junctionEdge = first ∨
    coloring normal.junctionEdge = second at crossSelected
  have selectedValue : coloring normal.junctionEdge ∈
      ({first, second} : Set Color) := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
      first, second, coloring] using crossSelected
  rcases normal.pairClassification with fixedThird | outerThird
  · apply Or.inl
    refine ⟨fixedThird, ?_⟩
    have selectedFixedThird : normal.junctionEdge ∈
        coloring.bicoloredSet fixed third := by
      rw [fixedThird] at selectedValue
      change coloring normal.junctionEdge = fixed ∨
        coloring normal.junctionEdge = third
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
        third, fixed, outer] using selectedValue
    exact coloring.color_eq_of_mem_two_bicoloredSets
      (Ne.symm (add_ne_right_of_ne_zero
        normal.returnData.lastOverlap.overlap.fixedColor_ne_zero))
      returnSelected selectedFixedThird
  · apply Or.inr
    refine ⟨outerThird, ?_⟩
    have selectedOuterThird : normal.junctionEdge ∈
        coloring.bicoloredSet outer third := by
      rw [outerThird] at selectedValue
      change coloring normal.junctionEdge = outer ∨
        coloring normal.junctionEdge = third
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
        third, fixed, outer] using selectedValue
    have returnSelected' : normal.junctionEdge ∈
        coloring.bicoloredSet outer fixed :=
      returnSelected.elim Or.inr Or.inl
    exact coloring.color_eq_of_mem_two_bicoloredSets
      (Ne.symm (add_ne_left_of_ne_zero
        normal.returnData.lastOverlap.overlap.breakOuterColor_ne_zero))
      returnSelected' selectedOuterThird

end CompanionCrossPairJunctionNormalForm

/-- A closed companion circuit has only four normalized outcomes: local
cancellation, a cross-pair junction with two aligned Kempe paths, a
shared-edge pivot, or full three-pair monodromy. -/
theorem closedCircuit_exists_localCancellation_or_crossPairJunction_or_edgePivot_or_threePairMonodromy
    (closed : Relation.TransGen
      (CompanionAdjacentEscapeTransition collar) start start) :
    Nonempty (CompanionCanonicalComponentDisjointClosure collar start) ∨
      Nonempty (CompanionCrossPairJunctionNormalForm collar start) ∨
        Nonempty (CompanionSameOuterTargetAvoidingEdgePivot collar start) ∨
          Nonempty (CompanionThreePairMonodromy collar start) := by
  rcases
      closedCircuit_exists_localCancellation_or_crossPairIntersection_or_componentContact_or_edgePivot_or_threePairMonodromy
        closed with hcancel | hintersection | hcontact | hpivot | hmonodromy
  · exact Or.inl hcancel
  · rcases hintersection with ⟨intersection⟩
    exact Or.inr (Or.inl ⟨intersection.toCrossPairJunctionNormalForm⟩)
  · rcases hcontact with ⟨contact⟩
    exact Or.inr (Or.inl contact.nonempty_crossPairJunctionNormalForm)
  · exact Or.inr (Or.inr (Or.inl hpivot))
  · exact Or.inr (Or.inr (Or.inr hmonodromy))

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
