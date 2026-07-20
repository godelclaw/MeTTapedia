import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentTransport

set_option autoImplicit false

namespace SimpleGraph.Coloring

universe u v

variable {Vertex : Type u} {Color : Type v}
  {G : SimpleGraph Vertex} [DecidableEq Color]

/-- A selected component avoiding a selected root is disjoint from the
canonical component containing that root. -/
theorem disjoint_kempeComponentSet_kempeComponentSetAtVertex_of_not_mem
    (coloring : G.Coloring Color) (first second : Color)
    (component :
      (coloring.bicoloredSubgraph first second).ConnectedComponent)
    (root : Vertex) (selected : root ∈
      coloring.bicoloredSet first second)
    (notMember : root ∉
      coloring.kempeComponentSet first second component) :
    Disjoint (coloring.kempeComponentSet first second component)
      (coloring.kempeComponentSetAtVertex first second root) := by
  rw [coloring.kempeComponentSetAtVertex_eq_of_mem
    first second root selected]
  let rootComponent :=
    (coloring.bicoloredSubgraph first second).connectedComponentMk
      ⟨root, selected⟩
  have component_ne : component ≠ rootComponent := by
    intro component_eq
    apply notMember
    rw [component_eq]
    exact coloring.mem_kempeComponentSet_self selected
  rw [Set.disjoint_left]
  intro vertex inComponent inRootComponent
  exact component_ne
    (coloring.kempeComponent_eq_of_common_vertex
      inComponent inRootComponent)

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

namespace CompanionSameOuterEdgeConstantReturn

variable (returnData : CompanionSameOuterEdgeConstantReturn collar start)

/-- Every state reached along the edge-constant suffix carries the common
root edge in the fixed outer color. -/
theorem suffixStateColor_eq_breakOuter
    {state : sourceNormal.KempeOrbitAdjacentEscape}
    (reachable : Relation.ReflTransGen returnData.suffixTransition
      returnData.lastOverlap.overlap.breakTarget state) :
    collar.sourceCommonColoring state
        returnData.lastOverlap.overlap.commonEdge =
      returnData.lastOverlap.overlap.breakOuterColor := by
  have endpointEq := reflTransGen_endpoint_eq_of_step_eq
    (fun escape : sourceNormal.KempeOrbitAdjacentEscape =>
      collar.sourceCommonColoring escape
        returnData.lastOverlap.overlap.commonEdge)
    reachable
  simpa only [CompanionSameOuterEdgeConstantReturn.suffixTransition,
    CompanionRepairBreakOverlap.breakOuterColor] using endpointEq.symm

end CompanionSameOuterEdgeConstantReturn

/-- One component-constant suffix step with an explicitly chosen selected
component disjoint from the canonical rooted component. -/
structure CompanionCanonicalComponentDisjointStep
    (closure : CompanionCanonicalSamePairClosure collar start)
    (source target : sourceNormal.KempeOrbitAdjacentEscape) where
  retained : closure.returnData.suffixTransition source target
  componentSet_eq :
    closure.returnData.canonicalReturnComponentSet source =
      closure.returnData.canonicalReturnComponentSet target
  step : CompanionAdjacentEscapeStep collar source
  successor_eq : step.successor = target
  selected_disjoint : Disjoint
    (source.coloring.kempeComponentSet
      (crossFaceZeroColor step.firstHit.transfer.coordinate)
      step.reentry.realization.companion
      step.reentry.realization.component)
    (closure.returnData.canonicalReturnComponentSet source)

/-- The exact residual branch in which every intervening component has a
chosen realization disjoint from the canonical rooted component. -/
structure CompanionCanonicalComponentDisjointClosure
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  closure : CompanionCanonicalSamePairClosure collar start
  path : Relation.ReflTransGen
    (fun source target => Nonempty
      (CompanionCanonicalComponentDisjointStep closure source target))
    closure.returnData.lastOverlap.overlap.breakTarget
    closure.returnData.lastOverlap.overlap.repairSource

/-- One exact component-constant suffix transition whose selected component
intersects the canonical rooted component. -/
structure CompanionCanonicalComponentIntersection
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  closure : CompanionCanonicalSamePairClosure collar start
  intersectionSource : sourceNormal.KempeOrbitAdjacentEscape
  intersectionTarget : sourceNormal.KempeOrbitAdjacentEscape
  reach_intersection : Relation.ReflTransGen
    (fun source target =>
      closure.returnData.suffixTransition source target ∧
        closure.returnData.canonicalReturnComponentSet source =
          closure.returnData.canonicalReturnComponentSet target)
    closure.returnData.lastOverlap.overlap.breakTarget intersectionSource
  reach_repair_after_intersection : Relation.ReflTransGen
    (fun source target =>
      closure.returnData.suffixTransition source target ∧
        closure.returnData.canonicalReturnComponentSet source =
          closure.returnData.canonicalReturnComponentSet target)
    intersectionTarget closure.returnData.lastOverlap.overlap.repairSource
  step : CompanionAdjacentEscapeStep collar intersectionSource
  successor_eq : step.successor = intersectionTarget
  retained :
    closure.returnData.suffixTransition intersectionSource intersectionTarget
  componentSet_eq :
    closure.returnData.canonicalReturnComponentSet intersectionSource =
      closure.returnData.canonicalReturnComponentSet intersectionTarget
  intersectionEdge :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).edgeSet
  intersectionEdge_mem_selected : intersectionEdge ∈
    intersectionSource.coloring.kempeComponentSet
      (crossFaceZeroColor step.firstHit.transfer.coordinate)
      step.reentry.realization.companion
      step.reentry.realization.component
  intersectionEdge_mem_canonical : intersectionEdge ∈
    closure.returnData.canonicalReturnComponentSet intersectionSource

/-- A canonical same-pair closure either transports through components
disjoint from the rooted component or contains one concrete intersection. -/
theorem CompanionCanonicalSamePairClosure.disjointClosure_or_intersection
    (closure : CompanionCanonicalSamePairClosure collar start) :
    Nonempty (CompanionCanonicalComponentDisjointClosure collar start) ∨
      Nonempty (CompanionCanonicalComponentIntersection collar start) := by
  let condition := fun source target :
      sourceNormal.KempeOrbitAdjacentEscape =>
    ∃ step : CompanionAdjacentEscapeStep collar source,
      step.successor = target ∧
        Disjoint
          (source.coloring.kempeComponentSet
            (crossFaceZeroColor step.firstHit.transfer.coordinate)
            step.reentry.realization.companion
            step.reentry.realization.component)
          (closure.returnData.canonicalReturnComponentSet source)
  rcases reflTransGen_lift_condition_or_exists_failure condition
      closure.constantReturn.path with
    hdisjoint | ⟨intersectionSource, intersectionTarget, hprefix,
      hintersection, hnotDisjoint, hsuffix⟩
  · apply Or.inl
    refine ⟨{
      closure := closure
      path := ?_ }⟩
    apply Relation.ReflTransGen.mono
      (r := fun source target =>
        (closure.returnData.suffixTransition source target ∧
          closure.returnData.canonicalReturnComponentSet source =
            closure.returnData.canonicalReturnComponentSet target) ∧
          condition source target)
    · intro source target retained
      rcases retained.2 with ⟨step, hsuccessor, hdisjoint⟩
      exact ⟨{
        retained := retained.1.1
        componentSet_eq := retained.1.2
        step := step
        successor_eq := hsuccessor
        selected_disjoint := hdisjoint }⟩
    · exact hdisjoint
  · rcases hintersection.1.1.1 with ⟨step, hsuccessor⟩
    have selectedNotDisjoint : ¬Disjoint
        (intersectionSource.coloring.kempeComponentSet
          (crossFaceZeroColor step.firstHit.transfer.coordinate)
          step.reentry.realization.companion
          step.reentry.realization.component)
        (closure.returnData.canonicalReturnComponentSet
          intersectionSource) := by
      intro hdisjoint
      exact hnotDisjoint ⟨step, hsuccessor, hdisjoint⟩
    rcases Set.not_disjoint_iff.mp selectedNotDisjoint with
      ⟨intersectionEdge, hselected, hcanonical⟩
    exact Or.inr ⟨{
      closure := closure
      intersectionSource := intersectionSource
      intersectionTarget := intersectionTarget
      reach_intersection := hprefix
      reach_repair_after_intersection := hsuffix
      step := step
      successor_eq := hsuccessor
      retained := hintersection.1
      componentSet_eq := hintersection.2
      intersectionEdge := intersectionEdge
      intersectionEdge_mem_selected := hselected
      intersectionEdge_mem_canonical := hcanonical }⟩

namespace CompanionCanonicalComponentDisjointStep

variable {closure : CompanionCanonicalSamePairClosure collar start}
  {source target : sourceNormal.KempeOrbitAdjacentEscape}

/-- A selected component disjoint from the canonical component leaves the
coloring pointwise fixed on that canonical component. -/
theorem coloring_eqOn_canonical
    (disjointStep :
      CompanionCanonicalComponentDisjointStep closure source target) :
    Set.EqOn source.coloring target.coloring
    (closure.returnData.canonicalReturnComponentSet source) := by
  intro edge edge_mem
  have edge_not_mem : edge ∉
      source.coloring.kempeComponentSet
        (crossFaceZeroColor disjointStep.step.firstHit.transfer.coordinate)
        disjointStep.step.reentry.realization.companion
        disjointStep.step.reentry.realization.component := by
    intro selected_mem
    exact (Set.disjoint_left.mp disjointStep.selected_disjoint)
      selected_mem edge_mem
  rw [← disjointStep.successor_eq, CompanionAdjacentEscapeStep.successor,
    disjointStep.step.reentry.coloring_eq,
    source.coloring.swapOnKempeComponent_apply_of_not_mem edge_not_mem]

end CompanionCanonicalComponentDisjointStep

namespace CompanionCanonicalComponentDisjointClosure

variable (disjointClosure :
  CompanionCanonicalComponentDisjointClosure collar start)

/-- A path of swaps disjoint from the moving canonical component preserves
both that component's ambient set and every color on it. -/
theorem pathColoring_eqOn_and_componentSet_eq
    {source target : sourceNormal.KempeOrbitAdjacentEscape}
    (path : Relation.ReflTransGen
      (fun before after => Nonempty
        (CompanionCanonicalComponentDisjointStep
          disjointClosure.closure before after)) source target) :
    Set.EqOn source.coloring target.coloring
        (disjointClosure.closure.returnData.canonicalReturnComponentSet
          source) ∧
      disjointClosure.closure.returnData.canonicalReturnComponentSet source =
        disjointClosure.closure.returnData.canonicalReturnComponentSet target := by
  induction path with
  | refl => exact ⟨fun _ _ => rfl, rfl⟩
  | @tail middle finish path retained ih =>
      rcases retained with ⟨step⟩
      constructor
      · intro edge edge_mem
        exact (ih.1 edge_mem).trans
          (step.coloring_eqOn_canonical (ih.2 ▸ edge_mem))
      · exact ih.2.trans step.componentSet_eq

/-- The entire residual suffix fixes the coloring pointwise on its exact
canonical rooted component. -/
theorem endpointColoring_eqOn_canonical : Set.EqOn
    disjointClosure.closure.returnData.lastOverlap.overlap.breakTarget.coloring
    disjointClosure.closure.returnData.lastOverlap.overlap.repairSource.coloring
    (disjointClosure.closure.returnData.canonicalReturnComponentSet
      disjointClosure.closure.returnData.lastOverlap.overlap.breakTarget) :=
  (disjointClosure.pathColoring_eqOn_and_componentSet_eq
    disjointClosure.path).1

/-- Equivalently, the suffix fixes every color on the exact selected break
component, which is also the exact selected repair component. -/
theorem endpointColoring_eqOn_breakComponent : Set.EqOn
    disjointClosure.closure.returnData.lastOverlap.overlap.breakTarget.coloring
    disjointClosure.closure.returnData.lastOverlap.overlap.repairSource.coloring
    disjointClosure.closure.breakComponentSet := by
  rw [disjointClosure.closure.breakComponentSet_eq_canonicalSource,
    disjointClosure.closure.canonicalSource_eq_canonicalBreakTarget]
  exact disjointClosure.endpointColoring_eqOn_canonical

/-- The disjoint branch is an exact local cancellation invariant: break and
repair select one ambient component, and the intervening suffix fixes every
color on it. -/
theorem breakRepairComponent_eq_and_endpointColoring_eqOn :
    disjointClosure.closure.breakComponentSet =
        disjointClosure.closure.repairComponentSet ∧
      Set.EqOn
        disjointClosure.closure.returnData.lastOverlap.overlap.breakTarget.coloring
        disjointClosure.closure.returnData.lastOverlap.overlap.repairSource.coloring
        disjointClosure.closure.breakComponentSet :=
  ⟨disjointClosure.closure.breakComponentSet_eq_repairComponentSet,
    disjointClosure.endpointColoring_eqOn_breakComponent⟩

end CompanionCanonicalComponentDisjointClosure

namespace CompanionCanonicalComponentIntersection

variable (intersection : CompanionCanonicalComponentIntersection collar start)

/-- The common root edge has the fixed outer color throughout the prefix to
the retained intersecting transition. -/
theorem rootColor_eq_breakOuter :
    intersection.intersectionSource.coloring
        (collar.commonEdgeInSource
          intersection.closure.returnData.lastOverlap.overlap.commonEdge) =
      intersection.closure.returnData.lastOverlap.overlap.breakOuterColor := by
  have reachable : Relation.ReflTransGen
      intersection.closure.returnData.suffixTransition
      intersection.closure.returnData.lastOverlap.overlap.breakTarget
      intersection.intersectionSource :=
    Relation.ReflTransGen.mono (fun _ _ retained => retained.1)
      intersection.reach_intersection
  simpa only [collar.sourceCommonColoring_apply_commonEdgeInSource] using
    intersection.closure.returnData.suffixStateColor_eq_breakOuter reachable

/-- Edge constancy forces the intersecting transition's selected component
to avoid the shared root edge itself. -/
theorem root_not_mem_selectedComponent :
    collar.commonEdgeInSource
          intersection.closure.returnData.lastOverlap.overlap.commonEdge ∉
      intersection.intersectionSource.coloring.kempeComponentSet
        (crossFaceZeroColor
          intersection.step.firstHit.transfer.coordinate)
        intersection.step.reentry.realization.companion
        intersection.step.reentry.realization.component := by
  apply intersection.step.commonEdge_not_mem_component_of_unchanged
    intersection.closure.returnData.lastOverlap.overlap.commonEdge
  rw [intersection.successor_eq]
  exact intersection.retained.2

/-- Since it avoids the root but meets the rooted component elsewhere, the
intersecting transition cannot use the enclosing return pair. -/
theorem selectedPair_ne_returnPair :
    ({crossFaceZeroColor intersection.step.firstHit.transfer.coordinate,
        intersection.step.reentry.realization.companion} : Set Color) ≠
      {intersection.closure.returnData.lastOverlap.overlap.fixedColor,
        intersection.closure.returnData.lastOverlap.overlap.breakOuterColor} := by
  intro pair_eq
  let first := crossFaceZeroColor
    intersection.step.firstHit.transfer.coordinate
  let second := intersection.step.reentry.realization.companion
  let fixed := intersection.closure.returnData.lastOverlap.overlap.fixedColor
  let outer :=
    intersection.closure.returnData.lastOverlap.overlap.breakOuterColor
  let root := collar.commonEdgeInSource
    intersection.closure.returnData.lastOverlap.overlap.commonEdge
  have first_mem : first = fixed ∨ first = outer := by
    have member : first ∈ ({first, second} : Set Color) := by simp
    rw [pair_eq] at member
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using member
  have second_mem : second = fixed ∨ second = outer := by
    have member : second ∈ ({first, second} : Set Color) := by simp
    rw [pair_eq] at member
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using member
  have root_selected_fixed_outer : root ∈
      intersection.intersectionSource.coloring.bicoloredSet fixed outer := by
    exact Or.inr intersection.rootColor_eq_breakOuter
  have contradict_disjoint (disjoint : Disjoint
      (intersection.intersectionSource.coloring.kempeComponentSet
        first second intersection.step.reentry.realization.component)
      (intersection.closure.returnData.canonicalReturnComponentSet
        intersection.intersectionSource)) : False :=
    (Set.disjoint_left.mp disjoint)
      intersection.intersectionEdge_mem_selected
      intersection.intersectionEdge_mem_canonical
  rcases first_mem with first_eq | first_eq <;>
    rcases second_mem with second_eq | second_eq
  · exact intersection.step.distinguished_ne_companion
      (first_eq.trans second_eq.symm)
  · have root_selected : root ∈
        intersection.intersectionSource.coloring.bicoloredSet first second := by
      simpa only [first, second, first_eq, second_eq] using
        root_selected_fixed_outer
    have disjoint := intersection.intersectionSource.coloring
      |>.disjoint_kempeComponentSet_kempeComponentSetAtVertex_of_not_mem
        first second intersection.step.reentry.realization.component root
        root_selected intersection.root_not_mem_selectedComponent
    apply contradict_disjoint
    simpa only [CompanionSameOuterEdgeConstantReturn.canonicalReturnComponentSet,
      first, second, fixed, outer, first_eq, second_eq, root] using disjoint
  · have root_selected : root ∈
        intersection.intersectionSource.coloring.bicoloredSet first second := by
      exact Or.inl (by
        simpa only [first, outer, first_eq] using
          intersection.rootColor_eq_breakOuter)
    have disjoint := intersection.intersectionSource.coloring
      |>.disjoint_kempeComponentSet_kempeComponentSetAtVertex_of_not_mem
        first second intersection.step.reentry.realization.component root
        root_selected intersection.root_not_mem_selectedComponent
    rw [intersection.intersectionSource.coloring
      |>.kempeComponentSetAtVertex_comm first second root] at disjoint
    apply contradict_disjoint
    simpa only [CompanionSameOuterEdgeConstantReturn.canonicalReturnComponentSet,
      first, second, fixed, outer, first_eq, second_eq, root] using disjoint
  · exact intersection.step.distinguished_ne_companion
      (first_eq.trans second_eq.symm)

/-- The retained intersection is exactly one of the two cross-color pairs:
fixed/third or outer/third. -/
theorem selectedPair_classification :
    ({crossFaceZeroColor intersection.step.firstHit.transfer.coordinate,
          intersection.step.reentry.realization.companion} : Set Color) =
        {intersection.closure.returnData.lastOverlap.overlap.fixedColor,
          intersection.closure.returnData.lastOverlap.overlap.fixedColor +
            intersection.closure.returnData.lastOverlap.overlap.breakOuterColor} ∨
      ({crossFaceZeroColor intersection.step.firstHit.transfer.coordinate,
          intersection.step.reentry.realization.companion} : Set Color) =
        {intersection.closure.returnData.lastOverlap.overlap.breakOuterColor,
          intersection.closure.returnData.lastOverlap.overlap.fixedColor +
            intersection.closure.returnData.lastOverlap.overlap.breakOuterColor} :=
  unorderedNonzeroPair_eq_leftSum_or_rightSum_of_ne
    intersection.closure.returnData.lastOverlap.overlap.fixedColor_ne_zero
    intersection.closure.returnData.lastOverlap.overlap.breakOuterColor_ne_zero
    (intersection.closure.returnData.lastOverlap.overlap
      |>.breakOuterColor_ne_fixedColor).symm
    (crossFaceZeroColor_ne_zero intersection.step.firstHit.transfer.coordinate)
    intersection.step.reentry.realization.companion_ne_zero
    intersection.step.distinguished_ne_companion
    intersection.selectedPair_ne_returnPair

end CompanionCanonicalComponentIntersection

/-- A closed circuit resolves into exact local cancellation, a classified
cross-pair intersection, a canonical-component change, a shared-edge pivot,
or full three-pair monodromy. -/
theorem closedCircuit_exists_localCancellation_or_crossPairIntersection_or_componentChange_or_edgePivot_or_threePairMonodromy
    (closed : Relation.TransGen
      (CompanionAdjacentEscapeTransition collar) start start) :
    Nonempty (CompanionCanonicalComponentDisjointClosure collar start) ∨
      Nonempty (CompanionCanonicalComponentIntersection collar start) ∨
        Nonempty (CompanionCanonicalSamePairComponentChange collar start) ∨
          Nonempty (CompanionSameOuterTargetAvoidingEdgePivot collar start) ∨
            Nonempty (CompanionThreePairMonodromy collar start) := by
  rcases
      closedCircuit_exists_canonicalSamePairClosure_or_componentChange_or_edgePivot_or_threePairMonodromy
        closed with hclosure | hchange | hpivot | hmonodromy
  · rcases hclosure with ⟨closure⟩
    rcases closure.disjointClosure_or_intersection with
      hdisjoint | hintersection
    · exact Or.inl hdisjoint
    · exact Or.inr (Or.inl hintersection)
  · exact Or.inr (Or.inr (Or.inl hchange))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpivot)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hmonodromy)))

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
