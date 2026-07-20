import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeMonodromy

set_option autoImplicit false

namespace SimpleGraph.Coloring

noncomputable section

universe u v

variable {Vertex : Type u} {Color : Type v}
  {G : SimpleGraph Vertex} [DecidableEq Color]

/-- The canonical selected-color component containing a vertex, returned as
an ambient vertex set.  It is empty when the root does not carry either
selected color. -/
def kempeComponentSetAtVertex
    (coloring : G.Coloring Color) (first second : Color)
    (root : Vertex) : Set Vertex :=
  if selected : coloring root = first ∨ coloring root = second then
    coloring.kempeComponentSet first second
      ((coloring.bicoloredSubgraph first second).connectedComponentMk
        ⟨root, selected⟩)
  else ∅

/-- At a selected root, the canonical set is literally the connected
component containing that root. -/
theorem kempeComponentSetAtVertex_eq_of_mem
    (coloring : G.Coloring Color) (first second : Color)
    (root : Vertex) (selected : root ∈
      coloring.bicoloredSet first second) :
    coloring.kempeComponentSetAtVertex first second root =
      coloring.kempeComponentSet first second
        ((coloring.bicoloredSubgraph first second).connectedComponentMk
          ⟨root, selected⟩) := by
  have selected' : coloring root = first ∨ coloring root = second := selected
  unfold kempeComponentSetAtVertex
  rw [dif_pos selected']

/-- A selected root belongs to its canonical component set. -/
theorem mem_kempeComponentSetAtVertex_of_mem
    (coloring : G.Coloring Color) (first second : Color)
    (root : Vertex) (selected : root ∈
      coloring.bicoloredSet first second) :
    root ∈ coloring.kempeComponentSetAtVertex first second root := by
  rw [coloring.kempeComponentSetAtVertex_eq_of_mem first second root selected]
  exact coloring.mem_kempeComponentSet_self selected

/-- Any selected component containing the root is the canonical rooted
component, at the level of ambient vertex sets. -/
theorem kempeComponentSet_eq_kempeComponentSetAtVertex_of_mem
    (coloring : G.Coloring Color) (first second : Color)
    (component :
      (coloring.bicoloredSubgraph first second).ConnectedComponent)
    (root : Vertex)
    (member : root ∈
      coloring.kempeComponentSet first second component) :
    coloring.kempeComponentSet first second component =
      coloring.kempeComponentSetAtVertex first second root := by
  have selected : root ∈ coloring.bicoloredSet first second :=
    coloring.mem_bicoloredSet_of_mem_kempeComponentSet member
  rw [coloring.kempeComponentSetAtVertex_eq_of_mem
    first second root selected]
  have component_eq : component =
      (coloring.bicoloredSubgraph first second).connectedComponentMk
        ⟨root, selected⟩ := by
    apply coloring.kempeComponent_eq_of_common_vertex member
    exact coloring.mem_kempeComponentSet_self selected
  rw [component_eq]

/-- Switching any component of a fixed color pair preserves the canonical
ambient component set rooted at every vertex. -/
theorem kempeComponentSetAtVertex_swapOnKempeComponent
    (coloring : G.Coloring Color) (first second : Color)
    (component :
      (coloring.bicoloredSubgraph first second).ConnectedComponent)
    (root : Vertex) :
    (coloring.swapOnKempeComponent first second component).kempeComponentSetAtVertex
        first second root =
      coloring.kempeComponentSetAtVertex first second root := by
  by_cases selected : root ∈ coloring.bicoloredSet first second
  · have selectedAfter : root ∈
        (coloring.swapOnKempeComponent first second component).bicoloredSet
          first second :=
      (coloring.mem_bicoloredSet_swapOnKempeComponent_iff
        first second component root).2 selected
    let rootComponent :=
      (coloring.bicoloredSubgraph first second).connectedComponentMk
        ⟨root, selected⟩
    let transported := coloring.transportKempeComponentAfterSwap
      first second component rootComponent
    let rootComponentAfter :=
      ((coloring.swapOnKempeComponent first second component).bicoloredSubgraph
          first second).connectedComponentMk
        ⟨root, selectedAfter⟩
    have hrootOld : root ∈ coloring.kempeComponentSet
        first second rootComponent := by
      exact coloring.mem_kempeComponentSet_self selected
    have hrootTransported : root ∈
        (coloring.swapOnKempeComponent first second component).kempeComponentSet
          first second transported := by
      exact (coloring.mem_kempeComponentSet_transportKempeComponentAfterSwap_iff
        first second component rootComponent root).2 hrootOld
    have hrootAfter : root ∈
        (coloring.swapOnKempeComponent first second component).kempeComponentSet
          first second rootComponentAfter := by
      exact (coloring.swapOnKempeComponent first second component)
        |>.mem_kempeComponentSet_self selectedAfter
    have hcomponent : rootComponentAfter = transported :=
      (coloring.swapOnKempeComponent first second component)
        |>.kempeComponent_eq_of_common_vertex hrootAfter hrootTransported
    rw [(coloring.swapOnKempeComponent first second component)
        |>.kempeComponentSetAtVertex_eq_of_mem first second root
          selectedAfter,
      coloring.kempeComponentSetAtVertex_eq_of_mem
        first second root selected]
    change (coloring.swapOnKempeComponent first second component).kempeComponentSet
        first second rootComponentAfter =
      coloring.kempeComponentSet first second rootComponent
    rw [hcomponent]
    exact coloring.kempeComponentSet_transportKempeComponentAfterSwap
      first second component rootComponent
  · have selectedAfter : root ∉
        (coloring.swapOnKempeComponent first second component).bicoloredSet
          first second := by
      intro hselected
      exact selected
        ((coloring.mem_bicoloredSet_swapOnKempeComponent_iff
          first second component root).1 hselected)
    have selectedValue :
        ¬(coloring root = first ∨ coloring root = second) := selected
    have selectedAfterValue :
        ¬((coloring.swapOnKempeComponent first second component) root = first ∨
          (coloring.swapOnKempeComponent first second component) root = second) :=
      selectedAfter
    unfold kempeComponentSetAtVertex
    rw [dif_neg selectedAfterValue, dif_neg selectedValue]

/-- Reversing the order of the two selected colors gives an identity-on-
vertices isomorphism of the two bicolored induced graphs. -/
def bicoloredSubgraphSwapIso
    (coloring : G.Coloring Color) (first second : Color) :
    coloring.bicoloredSubgraph first second ≃g
      coloring.bicoloredSubgraph second first where
  toFun vertex := ⟨vertex.1, vertex.2.elim Or.inr Or.inl⟩
  invFun vertex := ⟨vertex.1, vertex.2.elim Or.inr Or.inl⟩
  left_inv vertex := by ext; rfl
  right_inv vertex := by ext; rfl
  map_rel_iff' := by rfl

omit [DecidableEq Color] in
@[simp] theorem bicoloredSubgraphSwapIso_apply_val
    (coloring : G.Coloring Color) (first second : Color)
    (vertex : coloring.bicoloredSet first second) :
    (coloring.bicoloredSubgraphSwapIso first second vertex).1 = vertex.1 :=
  rfl

/-- The canonical rooted component set depends only on the unordered color
pair, not on its presentation order. -/
theorem kempeComponentSetAtVertex_comm
    (coloring : G.Coloring Color) (first second : Color)
    (root : Vertex) :
    coloring.kempeComponentSetAtVertex first second root =
      coloring.kempeComponentSetAtVertex second first root := by
  by_cases selected : root ∈ coloring.bicoloredSet first second
  · have selectedReverse : root ∈
        coloring.bicoloredSet second first := selected.elim Or.inr Or.inl
    rw [coloring.kempeComponentSetAtVertex_eq_of_mem
        first second root selected,
      coloring.kempeComponentSetAtVertex_eq_of_mem
        second first root selectedReverse]
    let iso := coloring.bicoloredSubgraphSwapIso first second
    ext vertex
    constructor
    · rintro ⟨vertexSelected, hcomponent⟩
      have vertexSelectedReverse : vertex ∈
          coloring.bicoloredSet second first :=
        vertexSelected.elim Or.inr Or.inl
      refine ⟨vertexSelectedReverse, ?_⟩
      calc
        (coloring.bicoloredSubgraph second first).connectedComponentMk
              ⟨vertex, vertexSelectedReverse⟩ =
            (coloring.bicoloredSubgraph second first).connectedComponentMk
              (iso ⟨vertex, vertexSelected⟩) := by congr 1
        _ = iso.connectedComponentEquiv
              ((coloring.bicoloredSubgraph first second).connectedComponentMk
                ⟨vertex, vertexSelected⟩) := by rfl
        _ = iso.connectedComponentEquiv
              ((coloring.bicoloredSubgraph first second).connectedComponentMk
                ⟨root, selected⟩) := congrArg _ hcomponent
        _ = (coloring.bicoloredSubgraph second first).connectedComponentMk
              (iso ⟨root, selected⟩) := by rfl
        _ = (coloring.bicoloredSubgraph second first).connectedComponentMk
              ⟨root, selectedReverse⟩ := by congr 1
    · rintro ⟨vertexSelected, hcomponent⟩
      have vertexSelectedReverse : vertex ∈
          coloring.bicoloredSet first second :=
        vertexSelected.elim Or.inr Or.inl
      refine ⟨vertexSelectedReverse, ?_⟩
      calc
        (coloring.bicoloredSubgraph first second).connectedComponentMk
              ⟨vertex, vertexSelectedReverse⟩ =
            (coloring.bicoloredSubgraph first second).connectedComponentMk
              (iso.symm ⟨vertex, vertexSelected⟩) := by congr 1
        _ = iso.symm.connectedComponentEquiv
              ((coloring.bicoloredSubgraph second first).connectedComponentMk
                ⟨vertex, vertexSelected⟩) := by rfl
        _ = iso.symm.connectedComponentEquiv
              ((coloring.bicoloredSubgraph second first).connectedComponentMk
                ⟨root, selectedReverse⟩) := congrArg _ hcomponent
        _ = (coloring.bicoloredSubgraph first second).connectedComponentMk
              (iso.symm ⟨root, selectedReverse⟩) := by rfl
        _ = (coloring.bicoloredSubgraph first second).connectedComponentMk
              ⟨root, selected⟩ := by congr 1
  · have selectedReverse : root ∉
        coloring.bicoloredSet second first := by
      intro hselected
      exact selected (hselected.elim Or.inr Or.inl)
    have selectedValue :
        ¬(coloring root = first ∨ coloring root = second) := selected
    have selectedReverseValue :
        ¬(coloring root = second ∨ coloring root = first) := selectedReverse
    unfold kempeComponentSetAtVertex
    rw [dif_neg selectedValue, dif_neg selectedReverseValue]

end
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

/-- A finite path whose every step preserves an observable has equal
observable values at its endpoints. -/
theorem reflTransGen_endpoint_eq_of_step_eq
    {State Value : Type*} {relation : State → State → Prop}
    (observable : State → Value) {start finish : State}
    (reachable : Relation.ReflTransGen
      (fun source target =>
        relation source target ∧ observable source = observable target)
      start finish) :
    observable start = observable finish := by
  induction reachable with
  | refl => rfl
  | tail _ retained ih => exact ih.trans retained.2

/-- Relative to two distinct nonzero Klein-four colors, every nonzero color
is the left color, the right color, or their sum. -/
theorem nonzeroColor_eq_left_or_right_or_sum
    {left right value : Color}
    (left_ne_zero : left ≠ 0) (right_ne_zero : right ≠ 0)
    (left_ne_right : left ≠ right) (value_ne_zero : value ≠ 0) :
    value = left ∨ value = right ∨ value = left + right := by
  by_cases value_eq_left : value = left
  · exact Or.inl value_eq_left
  · by_cases value_eq_right : value = right
    · exact Or.inr (Or.inl value_eq_right)
    · exact Or.inr (Or.inr
        (color_eq_add_of_three_distinct_nonzero value_ne_zero
          left_ne_zero right_ne_zero value_eq_left value_eq_right
          left_ne_right))

/-- A valid unordered nonzero color pair different from `{left,right}` is
exactly one of the two pairs involving the third color `left + right`. -/
theorem unorderedNonzeroPair_eq_leftSum_or_rightSum_of_ne
    {left right first second : Color}
    (left_ne_zero : left ≠ 0) (right_ne_zero : right ≠ 0)
    (left_ne_right : left ≠ right)
    (first_ne_zero : first ≠ 0) (second_ne_zero : second ≠ 0)
    (first_ne_second : first ≠ second)
    (pair_ne : ({first, second} : Set Color) ≠ {left, right}) :
    ({first, second} : Set Color) = {left, left + right} ∨
      ({first, second} : Set Color) = {right, left + right} := by
  rcases nonzeroColor_eq_left_or_right_or_sum left_ne_zero right_ne_zero
      left_ne_right first_ne_zero with
    rfl | rfl | rfl <;>
    rcases nonzeroColor_eq_left_or_right_or_sum left_ne_zero right_ne_zero
      left_ne_right second_ne_zero with rfl | rfl | rfl
  all_goals simp_all [Set.pair_comm]

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

/-- The canonical component set, in an arbitrary suffix state, of the fixed
same pair rooted at the distinguished common-core edge. -/
def CompanionSameOuterEdgeConstantReturn.canonicalReturnComponentSet
    (returnData : CompanionSameOuterEdgeConstantReturn collar start)
    (escape : sourceNormal.KempeOrbitAdjacentEscape) :
    Set (DeletedAdjacentPairGraph G
      collar.sourceData.firstVertex collar.sourceData.secondVertex).edgeSet :=
  escape.coloring.kempeComponentSetAtVertex
    returnData.lastOverlap.overlap.fixedColor
    returnData.lastOverlap.overlap.breakOuterColor
    (collar.commonEdgeInSource returnData.lastOverlap.overlap.commonEdge)

/-- The exact edge-constant, target-avoiding transition relation carried by
a same-outer return. -/
abbrev CompanionSameOuterEdgeConstantReturn.suffixTransition
    (returnData : CompanionSameOuterEdgeConstantReturn collar start)
    (source target : sourceNormal.KempeOrbitAdjacentEscape) : Prop :=
  (CompanionAdjacentEscapeTransition collar source target ∧
      collar.sourceCommonColoring target
            returnData.lastOverlap.overlap.commonEdge ≠
        collar.targetCommonColoring
          returnData.lastOverlap.overlap.commonEdge) ∧
    collar.sourceCommonColoring source
          returnData.lastOverlap.overlap.commonEdge =
      collar.sourceCommonColoring target
        returnData.lastOverlap.overlap.commonEdge

namespace CompanionSameOuterEdgeConstantReturn

variable (returnData : CompanionSameOuterEdgeConstantReturn collar start)

/-- The retained suffix is a path in its named edge-constant relation. -/
theorem suffixPath : Relation.ReflTransGen returnData.suffixTransition
    returnData.lastOverlap.overlap.breakTarget
    returnData.lastOverlap.overlap.repairSource := by
  simpa only [CompanionSameOuterEdgeConstantReturn.suffixTransition] using
    returnData.constantSuffix.path

end CompanionSameOuterEdgeConstantReturn

/-- A same-pair return whose canonical rooted component set is preserved at
every intervening transition. -/
structure CompanionCanonicalPairComponentConstantReturn
    (returnData : CompanionSameOuterEdgeConstantReturn collar start) where
  path : Relation.ReflTransGen
    (fun source target =>
      returnData.suffixTransition source target ∧
        returnData.canonicalReturnComponentSet source =
          returnData.canonicalReturnComponentSet target)
    returnData.lastOverlap.overlap.breakTarget
    returnData.lastOverlap.overlap.repairSource

namespace CompanionCanonicalPairComponentConstantReturn

variable {returnData : CompanionSameOuterEdgeConstantReturn collar start}

/-- Component-constant transport identifies the canonical rooted component
sets at the two ends of the intervening suffix. -/
theorem endpointComponentSet_eq :
    (constantReturn :
      CompanionCanonicalPairComponentConstantReturn returnData) →
    returnData.canonicalReturnComponentSet
        returnData.lastOverlap.overlap.breakTarget =
      returnData.canonicalReturnComponentSet
        returnData.lastOverlap.overlap.repairSource := by
  intro constantReturn
  exact reflTransGen_endpoint_eq_of_step_eq
    returnData.canonicalReturnComponentSet constantReturn.path

end CompanionCanonicalPairComponentConstantReturn

/-- One exact suffix transition where the canonical rooted same-pair
component set changes, with both remaining suffix segments retained. -/
structure CompanionCanonicalPairComponentChange
    (returnData : CompanionSameOuterEdgeConstantReturn collar start) where
  changeSource : sourceNormal.KempeOrbitAdjacentEscape
  changeTarget : sourceNormal.KempeOrbitAdjacentEscape
  reach_change : Relation.ReflTransGen returnData.suffixTransition
    returnData.lastOverlap.overlap.breakTarget changeSource
  changeTransition : returnData.suffixTransition changeSource changeTarget
  componentSet_ne :
    returnData.canonicalReturnComponentSet changeSource ≠
      returnData.canonicalReturnComponentSet changeTarget
  reach_repair_after_change : Relation.ReflTransGen
    returnData.suffixTransition changeTarget
      returnData.lastOverlap.overlap.repairSource

namespace CompanionCanonicalPairComponentChange

variable {returnData : CompanionSameOuterEdgeConstantReturn collar start}
  (change : CompanionCanonicalPairComponentChange returnData)

/-- The component-changing transition retains an actual selected component,
and edge constancy forces that selected component to avoid the root edge. -/
theorem exists_step_component_avoids_edge :
    ∃ step : CompanionAdjacentEscapeStep collar change.changeSource,
      step.successor = change.changeTarget ∧
        collar.commonEdgeInSource
              returnData.lastOverlap.overlap.commonEdge ∉
          change.changeSource.coloring.kempeComponentSet
            (crossFaceZeroColor step.firstHit.transfer.coordinate)
            step.reentry.realization.companion
            step.reentry.realization.component := by
  exact
    CompanionTargetAvoidingEdgeConstantSuffix.transition_exists_component_avoiding_edge
      change.changeTransition

/-- If the changing transition selected the return pair in the same order,
the canonical rooted component set could not change. -/
theorem componentSet_eq_of_stepPair_eq
    (step : CompanionAdjacentEscapeStep collar change.changeSource)
    (successor_eq : step.successor = change.changeTarget)
    (first_eq :
      crossFaceZeroColor step.firstHit.transfer.coordinate =
        returnData.lastOverlap.overlap.fixedColor)
    (second_eq : step.reentry.realization.companion =
      returnData.lastOverlap.overlap.breakOuterColor) :
    returnData.canonicalReturnComponentSet change.changeSource =
      returnData.canonicalReturnComponentSet change.changeTarget := by
  have coloring_eq : change.changeTarget.coloring =
      change.changeSource.coloring.swapOnKempeComponent
        (crossFaceZeroColor step.firstHit.transfer.coordinate)
        step.reentry.realization.companion
        step.reentry.realization.component := by
    calc
      change.changeTarget.coloring = step.successor.coloring :=
        congrArg (fun escape => escape.coloring) successor_eq.symm
      _ = step.reentry.realization.coloring := by
        simpa only [CompanionAdjacentEscapeStep.successor] using
          step.reentry.coloring_eq
      _ = change.changeSource.coloring.swapOnKempeComponent
          (crossFaceZeroColor step.firstHit.transfer.coordinate)
          step.reentry.realization.companion
          step.reentry.realization.component := rfl
  change change.changeSource.coloring.kempeComponentSetAtVertex
      returnData.lastOverlap.overlap.fixedColor
      returnData.lastOverlap.overlap.breakOuterColor
      (collar.commonEdgeInSource
        returnData.lastOverlap.overlap.commonEdge) =
    change.changeTarget.coloring.kempeComponentSetAtVertex
      returnData.lastOverlap.overlap.fixedColor
      returnData.lastOverlap.overlap.breakOuterColor
      (collar.commonEdgeInSource
        returnData.lastOverlap.overlap.commonEdge)
  rw [← first_eq, ← second_eq, coloring_eq]
  exact (change.changeSource.coloring
    |>.kempeComponentSetAtVertex_swapOnKempeComponent
      (crossFaceZeroColor step.firstHit.transfer.coordinate)
      step.reentry.realization.companion
      step.reentry.realization.component
      (collar.commonEdgeInSource
        returnData.lastOverlap.overlap.commonEdge)).symm

/-- The same conclusion holds when the transition presents the return pair
in reverse order. -/
theorem componentSet_eq_of_stepPair_eq_reverse
    (step : CompanionAdjacentEscapeStep collar change.changeSource)
    (successor_eq : step.successor = change.changeTarget)
    (first_eq :
      crossFaceZeroColor step.firstHit.transfer.coordinate =
        returnData.lastOverlap.overlap.breakOuterColor)
    (second_eq : step.reentry.realization.companion =
      returnData.lastOverlap.overlap.fixedColor) :
    returnData.canonicalReturnComponentSet change.changeSource =
      returnData.canonicalReturnComponentSet change.changeTarget := by
  have coloring_eq : change.changeTarget.coloring =
      change.changeSource.coloring.swapOnKempeComponent
        (crossFaceZeroColor step.firstHit.transfer.coordinate)
        step.reentry.realization.companion
        step.reentry.realization.component := by
    calc
      change.changeTarget.coloring = step.successor.coloring :=
        congrArg (fun escape => escape.coloring) successor_eq.symm
      _ = step.reentry.realization.coloring := by
        simpa only [CompanionAdjacentEscapeStep.successor] using
          step.reentry.coloring_eq
      _ = change.changeSource.coloring.swapOnKempeComponent
          (crossFaceZeroColor step.firstHit.transfer.coordinate)
          step.reentry.realization.companion
          step.reentry.realization.component := rfl
  change change.changeSource.coloring.kempeComponentSetAtVertex
      returnData.lastOverlap.overlap.fixedColor
      returnData.lastOverlap.overlap.breakOuterColor
      (collar.commonEdgeInSource
        returnData.lastOverlap.overlap.commonEdge) =
    change.changeTarget.coloring.kempeComponentSetAtVertex
      returnData.lastOverlap.overlap.fixedColor
      returnData.lastOverlap.overlap.breakOuterColor
      (collar.commonEdgeInSource
        returnData.lastOverlap.overlap.commonEdge)
  calc
    change.changeSource.coloring.kempeComponentSetAtVertex
          returnData.lastOverlap.overlap.fixedColor
          returnData.lastOverlap.overlap.breakOuterColor
          (collar.commonEdgeInSource
            returnData.lastOverlap.overlap.commonEdge) =
        change.changeSource.coloring.kempeComponentSetAtVertex
          returnData.lastOverlap.overlap.breakOuterColor
          returnData.lastOverlap.overlap.fixedColor
          (collar.commonEdgeInSource
            returnData.lastOverlap.overlap.commonEdge) :=
      change.changeSource.coloring.kempeComponentSetAtVertex_comm _ _ _
    _ = change.changeTarget.coloring.kempeComponentSetAtVertex
          returnData.lastOverlap.overlap.breakOuterColor
          returnData.lastOverlap.overlap.fixedColor
          (collar.commonEdgeInSource
            returnData.lastOverlap.overlap.commonEdge) := by
      rw [← first_eq, ← second_eq, coloring_eq]
      exact (change.changeSource.coloring
        |>.kempeComponentSetAtVertex_swapOnKempeComponent
          (crossFaceZeroColor step.firstHit.transfer.coordinate)
          step.reentry.realization.companion
          step.reentry.realization.component
          (collar.commonEdgeInSource
            returnData.lastOverlap.overlap.commonEdge)).symm
    _ = change.changeTarget.coloring.kempeComponentSetAtVertex
          returnData.lastOverlap.overlap.fixedColor
          returnData.lastOverlap.overlap.breakOuterColor
          (collar.commonEdgeInSource
            returnData.lastOverlap.overlap.commonEdge) :=
      (change.changeTarget.coloring.kempeComponentSetAtVertex_comm _ _ _).symm

/-- A transition changing the canonical rooted component must select a
genuinely different unordered color pair from the enclosing return pair. -/
theorem stepPair_ne_returnPair
    (step : CompanionAdjacentEscapeStep collar change.changeSource)
    (successor_eq : step.successor = change.changeTarget) :
    ({crossFaceZeroColor step.firstHit.transfer.coordinate,
        step.reentry.realization.companion} : Set Color) ≠
      {returnData.lastOverlap.overlap.fixedColor,
        returnData.lastOverlap.overlap.breakOuterColor} := by
  intro pair_eq
  have hfirst :
      crossFaceZeroColor step.firstHit.transfer.coordinate =
          returnData.lastOverlap.overlap.fixedColor ∨
        crossFaceZeroColor step.firstHit.transfer.coordinate =
          returnData.lastOverlap.overlap.breakOuterColor := by
    have hmem : crossFaceZeroColor step.firstHit.transfer.coordinate ∈
        ({crossFaceZeroColor step.firstHit.transfer.coordinate,
          step.reentry.realization.companion} : Set Color) := by simp
    rw [pair_eq] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hsecond :
      step.reentry.realization.companion =
          returnData.lastOverlap.overlap.fixedColor ∨
        step.reentry.realization.companion =
          returnData.lastOverlap.overlap.breakOuterColor := by
    have hmem : step.reentry.realization.companion ∈
        ({crossFaceZeroColor step.firstHit.transfer.coordinate,
          step.reentry.realization.companion} : Set Color) := by simp
    rw [pair_eq] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  rcases hfirst with hfirst | hfirst <;>
    rcases hsecond with hsecond | hsecond
  · exact step.distinguished_ne_companion (hfirst.trans hsecond.symm)
  · exact change.componentSet_ne
      (change.componentSet_eq_of_stepPair_eq step successor_eq
        hfirst hsecond)
  · exact change.componentSet_ne
      (change.componentSet_eq_of_stepPair_eq_reverse step successor_eq
        hfirst hsecond)
  · exact step.distinguished_ne_companion (hfirst.trans hsecond.symm)

/-- The component-change branch exposes a concrete cross-pair transition:
its selected component avoids the root edge while its unordered pair differs
from the rooted return pair. -/
theorem exists_crossPair_step_component_avoids_edge :
    ∃ step : CompanionAdjacentEscapeStep collar change.changeSource,
      step.successor = change.changeTarget ∧
        ({crossFaceZeroColor step.firstHit.transfer.coordinate,
            step.reentry.realization.companion} : Set Color) ≠
          {returnData.lastOverlap.overlap.fixedColor,
            returnData.lastOverlap.overlap.breakOuterColor} ∧
        collar.commonEdgeInSource
              returnData.lastOverlap.overlap.commonEdge ∉
          change.changeSource.coloring.kempeComponentSet
            (crossFaceZeroColor step.firstHit.transfer.coordinate)
            step.reentry.realization.companion
            step.reentry.realization.component := by
  rcases change.exists_step_component_avoids_edge with
    ⟨step, hsuccessor, havoids⟩
  exact ⟨step, hsuccessor,
    change.stepPair_ne_returnPair step hsuccessor, havoids⟩

/-- The concrete cross-pair interaction is exactly one of the two remaining
Klein-four pairs: fixed/third or outer/third. -/
theorem exists_crossPair_step_classification :
    ∃ step : CompanionAdjacentEscapeStep collar change.changeSource,
      step.successor = change.changeTarget ∧
        (({crossFaceZeroColor step.firstHit.transfer.coordinate,
              step.reentry.realization.companion} : Set Color) =
            {returnData.lastOverlap.overlap.fixedColor,
              returnData.lastOverlap.overlap.fixedColor +
                returnData.lastOverlap.overlap.breakOuterColor} ∨
          ({crossFaceZeroColor step.firstHit.transfer.coordinate,
              step.reentry.realization.companion} : Set Color) =
            {returnData.lastOverlap.overlap.breakOuterColor,
              returnData.lastOverlap.overlap.fixedColor +
                returnData.lastOverlap.overlap.breakOuterColor}) ∧
        collar.commonEdgeInSource
              returnData.lastOverlap.overlap.commonEdge ∉
          change.changeSource.coloring.kempeComponentSet
            (crossFaceZeroColor step.firstHit.transfer.coordinate)
            step.reentry.realization.companion
            step.reentry.realization.component := by
  rcases change.exists_crossPair_step_component_avoids_edge with
    ⟨step, hsuccessor, hpairNe, havoids⟩
  have hclassification :=
    unorderedNonzeroPair_eq_leftSum_or_rightSum_of_ne
      returnData.lastOverlap.overlap.fixedColor_ne_zero
      returnData.lastOverlap.overlap.breakOuterColor_ne_zero
      returnData.lastOverlap.overlap.breakOuterColor_ne_fixedColor.symm
      (crossFaceZeroColor_ne_zero step.firstHit.transfer.coordinate)
      step.reentry.realization.companion_ne_zero
      step.distinguished_ne_companion hpairNe
  exact ⟨step, hsuccessor, hclassification, havoids⟩

end CompanionCanonicalPairComponentChange

/-- The canonical rooted same-pair component either transports unchanged
through the whole suffix or changes at one retained transition. -/
theorem CompanionSameOuterEdgeConstantReturn.componentConstant_or_change
    (returnData : CompanionSameOuterEdgeConstantReturn collar start) :
    Nonempty (CompanionCanonicalPairComponentConstantReturn returnData) ∨
      Nonempty (CompanionCanonicalPairComponentChange returnData) := by
  let condition := fun source target :
      sourceNormal.KempeOrbitAdjacentEscape =>
    returnData.canonicalReturnComponentSet source =
      returnData.canonicalReturnComponentSet target
  rcases reflTransGen_lift_condition_or_exists_failure condition
      returnData.suffixPath with
    hconstant | ⟨changeSource, changeTarget, hprefix, hchange,
      hsets, hsuffix⟩
  · exact Or.inl ⟨{
      path := by simpa only [condition] using hconstant }⟩
  · exact Or.inr ⟨{
      changeSource := changeSource
      changeTarget := changeTarget
      reach_change := hprefix
      changeTransition := hchange
      componentSet_ne := hsets
      reach_repair_after_change := hsuffix }⟩

/-- The residual same-pair branch with exact canonical rooted-component
transport across its full intervening suffix. -/
structure CompanionCanonicalSamePairClosure
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  returnData : CompanionSameOuterEdgeConstantReturn collar start
  constantReturn :
    CompanionCanonicalPairComponentConstantReturn returnData

namespace CompanionCanonicalSamePairClosure

variable (closure : CompanionCanonicalSamePairClosure collar start)

/-- Ambient edge set of the selected break component. -/
def breakComponentSet :
    Set (DeletedAdjacentPairGraph G
      collar.sourceData.firstVertex collar.sourceData.secondVertex).edgeSet :=
  closure.returnData.lastOverlap.overlap.breakSource.coloring.kempeComponentSet
    (crossFaceZeroColor
      closure.returnData.lastOverlap.overlap.breakStep.firstHit.transfer.coordinate)
    closure.returnData.lastOverlap.overlap.breakStep.reentry.realization.companion
    closure.returnData.lastOverlap.overlap.breakStep.reentry.realization.component

/-- Ambient edge set of the selected repair component. -/
def repairComponentSet :
    Set (DeletedAdjacentPairGraph G
      collar.sourceData.firstVertex collar.sourceData.secondVertex).edgeSet :=
  closure.returnData.lastOverlap.overlap.repairSource.coloring.kempeComponentSet
    (crossFaceZeroColor
      closure.returnData.lastOverlap.overlap.repairStep.firstHit.transfer.coordinate)
    closure.returnData.lastOverlap.overlap.repairStep.reentry.realization.companion
    closure.returnData.lastOverlap.overlap.repairStep.reentry.realization.component

/-- The canonical rooted component has exactly the same ambient edge set at
the two ends of the intervening suffix. -/
theorem endpointComponentSet_eq :
    closure.returnData.canonicalReturnComponentSet
        closure.returnData.lastOverlap.overlap.breakTarget =
      closure.returnData.canonicalReturnComponentSet
        closure.returnData.lastOverlap.overlap.repairSource :=
  CompanionCanonicalPairComponentConstantReturn.endpointComponentSet_eq
    closure.constantReturn

/-- The enclosing break and repair use the same unordered selected pair. -/
theorem repairPair_eq_breakPair :
    ({crossFaceZeroColor
          closure.returnData.lastOverlap.overlap.repairStep.firstHit.transfer.coordinate,
        closure.returnData.lastOverlap.overlap.repairStep.reentry.realization.companion} :
        Set Color) =
      {crossFaceZeroColor
          closure.returnData.lastOverlap.overlap.breakStep.firstHit.transfer.coordinate,
        closure.returnData.lastOverlap.overlap.breakStep.reentry.realization.companion} :=
  closure.returnData.lastOverlap.overlap
    |>.repairPair_eq_breakPair_of_sameOuter closure.returnData.sameOuter

/-- The selected break component is the canonical rooted return-pair
component in the break source coloring. -/
theorem breakComponentSet_eq_canonicalSource :
    closure.breakComponentSet =
      closure.returnData.canonicalReturnComponentSet
        closure.returnData.lastOverlap.overlap.breakSource := by
  let overlap := closure.returnData.lastOverlap.overlap
  let root := collar.commonEdgeInSource overlap.commonEdge
  have selectedEq := overlap.breakSource.coloring
    |>.kempeComponentSet_eq_kempeComponentSetAtVertex_of_mem
      (crossFaceZeroColor overlap.breakStep.firstHit.transfer.coordinate)
      overlap.breakStep.reentry.realization.companion
      overlap.breakStep.reentry.realization.component root
      overlap.breakEdge_mem_component
  rcases overlap.breakPair_orientation with orientation | orientation
  · simpa only [breakComponentSet,
      CompanionSameOuterEdgeConstantReturn.canonicalReturnComponentSet,
      overlap, root, orientation.1, orientation.2] using selectedEq
  · calc
      closure.breakComponentSet =
          overlap.breakSource.coloring.kempeComponentSetAtVertex
            (crossFaceZeroColor
              overlap.breakStep.firstHit.transfer.coordinate)
            overlap.breakStep.reentry.realization.companion root := by
        simpa only [breakComponentSet, overlap, root] using selectedEq
      _ = overlap.breakSource.coloring.kempeComponentSetAtVertex
            overlap.breakOuterColor overlap.fixedColor root := by
        rw [orientation.2, orientation.1]
      _ = overlap.breakSource.coloring.kempeComponentSetAtVertex
            overlap.fixedColor overlap.breakOuterColor root :=
        (overlap.breakSource.coloring
          |>.kempeComponentSetAtVertex_comm
            overlap.fixedColor overlap.breakOuterColor root).symm
      _ = closure.returnData.canonicalReturnComponentSet
            overlap.breakSource := rfl

/-- The canonical rooted return-pair component survives the enclosing break
swap as the same ambient edge set. -/
theorem canonicalSource_eq_canonicalBreakTarget :
    closure.returnData.canonicalReturnComponentSet
        closure.returnData.lastOverlap.overlap.breakSource =
      closure.returnData.canonicalReturnComponentSet
        closure.returnData.lastOverlap.overlap.breakTarget := by
  let overlap := closure.returnData.lastOverlap.overlap
  let root := collar.commonEdgeInSource overlap.commonEdge
  have coloring_eq : overlap.breakTarget.coloring =
      overlap.breakSource.coloring.swapOnKempeComponent
        (crossFaceZeroColor overlap.breakStep.firstHit.transfer.coordinate)
        overlap.breakStep.reentry.realization.companion
        overlap.breakStep.reentry.realization.component := by
    calc
      overlap.breakTarget.coloring = overlap.breakStep.successor.coloring :=
        congrArg (fun escape => escape.coloring)
          overlap.break_successor_eq.symm
      _ = overlap.breakStep.reentry.realization.coloring := by
        simpa only [CompanionAdjacentEscapeStep.successor] using
          overlap.breakStep.reentry.coloring_eq
      _ = overlap.breakSource.coloring.swapOnKempeComponent
          (crossFaceZeroColor overlap.breakStep.firstHit.transfer.coordinate)
          overlap.breakStep.reentry.realization.companion
          overlap.breakStep.reentry.realization.component := rfl
  change overlap.breakSource.coloring.kempeComponentSetAtVertex
      overlap.fixedColor overlap.breakOuterColor root =
    overlap.breakTarget.coloring.kempeComponentSetAtVertex
      overlap.fixedColor overlap.breakOuterColor root
  rcases overlap.breakPair_orientation with orientation | orientation
  · rw [orientation.1, orientation.2, coloring_eq]
    exact (overlap.breakSource.coloring
      |>.kempeComponentSetAtVertex_swapOnKempeComponent
        (crossFaceZeroColor overlap.breakStep.firstHit.transfer.coordinate)
        overlap.breakStep.reentry.realization.companion
        overlap.breakStep.reentry.realization.component root).symm
  · calc
      overlap.breakSource.coloring.kempeComponentSetAtVertex
            overlap.fixedColor overlap.breakOuterColor root =
          overlap.breakSource.coloring.kempeComponentSetAtVertex
            overlap.breakOuterColor overlap.fixedColor root :=
        overlap.breakSource.coloring.kempeComponentSetAtVertex_comm _ _ _
      _ = overlap.breakTarget.coloring.kempeComponentSetAtVertex
            overlap.breakOuterColor overlap.fixedColor root := by
        rw [orientation.2, orientation.1, coloring_eq]
        exact (overlap.breakSource.coloring
          |>.kempeComponentSetAtVertex_swapOnKempeComponent
            (crossFaceZeroColor
              overlap.breakStep.firstHit.transfer.coordinate)
            overlap.breakStep.reentry.realization.companion
            overlap.breakStep.reentry.realization.component root).symm
      _ = overlap.breakTarget.coloring.kempeComponentSetAtVertex
            overlap.fixedColor overlap.breakOuterColor root :=
        (overlap.breakTarget.coloring
          |>.kempeComponentSetAtVertex_comm _ _ _).symm

/-- The selected repair component is the canonical rooted return-pair
component in the repair source coloring. -/
theorem repairComponentSet_eq_canonicalSource :
    closure.repairComponentSet =
      closure.returnData.canonicalReturnComponentSet
        closure.returnData.lastOverlap.overlap.repairSource := by
  let overlap := closure.returnData.lastOverlap.overlap
  let root := collar.commonEdgeInSource overlap.commonEdge
  have selectedEq := overlap.repairSource.coloring
    |>.kempeComponentSet_eq_kempeComponentSetAtVertex_of_mem
      (crossFaceZeroColor overlap.repairStep.firstHit.transfer.coordinate)
      overlap.repairStep.reentry.realization.companion
      overlap.repairStep.reentry.realization.component root
      overlap.repairEdge_mem_component
  rcases overlap.repairPair_orientation with orientation | orientation
  · calc
      closure.repairComponentSet =
          overlap.repairSource.coloring.kempeComponentSetAtVertex
            (crossFaceZeroColor
              overlap.repairStep.firstHit.transfer.coordinate)
            overlap.repairStep.reentry.realization.companion root := by
        simpa only [repairComponentSet, overlap, root] using selectedEq
      _ = overlap.repairSource.coloring.kempeComponentSetAtVertex
            overlap.repairOuterColor overlap.fixedColor root := by
        rw [orientation.1, orientation.2]
      _ = overlap.repairSource.coloring.kempeComponentSetAtVertex
            overlap.fixedColor overlap.repairOuterColor root :=
        (overlap.repairSource.coloring
          |>.kempeComponentSetAtVertex_comm _ _ _).symm
      _ = closure.returnData.canonicalReturnComponentSet
            overlap.repairSource := by
        rw [closure.returnData.sameOuter]
        rfl
  · have distinguished_eq :
        crossFaceZeroColor
            overlap.repairStep.firstHit.transfer.coordinate =
          overlap.fixedColor := orientation.2.symm
    have companion_eq : overlap.repairStep.reentry.realization.companion =
        overlap.breakOuterColor :=
      orientation.1.symm.trans closure.returnData.sameOuter
    simpa only [repairComponentSet,
      CompanionSameOuterEdgeConstantReturn.canonicalReturnComponentSet,
      overlap, root, distinguished_eq, companion_eq] using selectedEq

/-- In the canonical-constant branch, the enclosing break and repair are
the same ambient component as well as the same unordered color pair. -/
theorem breakComponentSet_eq_repairComponentSet :
    closure.breakComponentSet = closure.repairComponentSet := by
  calc
    closure.breakComponentSet =
        closure.returnData.canonicalReturnComponentSet
          closure.returnData.lastOverlap.overlap.breakSource :=
      closure.breakComponentSet_eq_canonicalSource
    _ = closure.returnData.canonicalReturnComponentSet
          closure.returnData.lastOverlap.overlap.breakTarget :=
      closure.canonicalSource_eq_canonicalBreakTarget
    _ = closure.returnData.canonicalReturnComponentSet
          closure.returnData.lastOverlap.overlap.repairSource :=
      closure.endpointComponentSet_eq
    _ = closure.repairComponentSet :=
      closure.repairComponentSet_eq_canonicalSource.symm

end CompanionCanonicalSamePairClosure

/-- The residual same-pair branch with one exact external transition which
changes the canonical rooted component while its own component avoids the
root edge. -/
structure CompanionCanonicalSamePairComponentChange
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  returnData : CompanionSameOuterEdgeConstantReturn collar start
  change : CompanionCanonicalPairComponentChange returnData

/-- Every closed companion circuit now yields canonical same-pair closure,
a rooted-component interaction, a shared-edge nonfixed pivot, or full
three-pair monodromy. -/
theorem closedCircuit_exists_canonicalSamePairClosure_or_componentChange_or_edgePivot_or_threePairMonodromy
    (closed : Relation.TransGen
      (CompanionAdjacentEscapeTransition collar) start start) :
    Nonempty (CompanionCanonicalSamePairClosure collar start) ∨
      Nonempty (CompanionCanonicalSamePairComponentChange collar start) ∨
        Nonempty (CompanionSameOuterTargetAvoidingEdgePivot collar start) ∨
          Nonempty (CompanionThreePairMonodromy collar start) := by
  rcases
      closedCircuit_exists_sameOuterEdgeConstantReturn_or_edgePivot_or_threePairMonodromy
        closed with hreturn | hpivot | hmonodromy
  · rcases hreturn with ⟨returnData⟩
    rcases returnData.componentConstant_or_change with
      hconstant | hchange
    · rcases hconstant with ⟨constantReturn⟩
      exact Or.inl ⟨{
        returnData := returnData
        constantReturn := constantReturn }⟩
    · rcases hchange with ⟨change⟩
      exact Or.inr (Or.inl ⟨{
        returnData := returnData
        change := change }⟩)
  · exact Or.inr (Or.inr (Or.inl hpivot))
  · exact Or.inr (Or.inr (Or.inr hmonodromy))

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
