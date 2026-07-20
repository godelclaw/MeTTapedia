import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentJunction

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

/-- A canonical-component-changing branch with one concrete edge witnessing
the symmetric difference, together with its actual classified Kempe step. -/
structure CompanionCanonicalComponentDifference
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  componentChange : CompanionCanonicalSamePairComponentChange collar start
  step : CompanionAdjacentEscapeStep collar
    componentChange.change.changeSource
  successor_eq : step.successor = componentChange.change.changeTarget
  pairClassification :
    (({crossFaceZeroColor step.firstHit.transfer.coordinate,
          step.reentry.realization.companion} : Set Color) =
        {componentChange.returnData.lastOverlap.overlap.fixedColor,
          componentChange.returnData.lastOverlap.overlap.fixedColor +
            componentChange.returnData.lastOverlap.overlap.breakOuterColor} ∨
      ({crossFaceZeroColor step.firstHit.transfer.coordinate,
          step.reentry.realization.companion} : Set Color) =
        {componentChange.returnData.lastOverlap.overlap.breakOuterColor,
          componentChange.returnData.lastOverlap.overlap.fixedColor +
            componentChange.returnData.lastOverlap.overlap.breakOuterColor})
  root_not_mem_selectedComponent :
    collar.commonEdgeInSource
          componentChange.returnData.lastOverlap.overlap.commonEdge ∉
      componentChange.change.changeSource.coloring.kempeComponentSet
        (crossFaceZeroColor step.firstHit.transfer.coordinate)
        step.reentry.realization.companion
        step.reentry.realization.component
  differenceEdge :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).edgeSet
  membershipChange :
    (differenceEdge ∈
          componentChange.returnData.canonicalReturnComponentSet
            componentChange.change.changeSource ∧
        differenceEdge ∉
          componentChange.returnData.canonicalReturnComponentSet
            componentChange.change.changeTarget) ∨
      (differenceEdge ∉
          componentChange.returnData.canonicalReturnComponentSet
            componentChange.change.changeSource ∧
        differenceEdge ∈
          componentChange.returnData.canonicalReturnComponentSet
            componentChange.change.changeTarget)

/-- Every canonical-component change has an exact symmetric-difference
witness and retains the classified cross-pair step causing it. -/
theorem nonempty_companionCanonicalComponentDifference
    (componentChange :
      CompanionCanonicalSamePairComponentChange collar start) :
    Nonempty (CompanionCanonicalComponentDifference collar start) := by
  rcases componentChange.change.exists_crossPair_step_classification with
    ⟨step, successor_eq, pairClassification, root_not_mem⟩
  let sourceSet := componentChange.returnData.canonicalReturnComponentSet
    componentChange.change.changeSource
  let targetSet := componentChange.returnData.canonicalReturnComponentSet
    componentChange.change.changeTarget
  have set_ne : sourceSet ≠ targetSet :=
    componentChange.change.componentSet_ne
  by_cases source_subset : sourceSet ⊆ targetSet
  · have target_not_subset : ¬targetSet ⊆ sourceSet := by
      intro target_subset
      exact set_ne (Set.Subset.antisymm source_subset target_subset)
    rcases Set.not_subset.mp target_not_subset with
      ⟨differenceEdge, target_mem, source_not_mem⟩
    exact ⟨{
      componentChange := componentChange
      step := step
      successor_eq := successor_eq
      pairClassification := pairClassification
      root_not_mem_selectedComponent := root_not_mem
      differenceEdge := differenceEdge
      membershipChange := Or.inr ⟨source_not_mem, target_mem⟩ }⟩
  · rcases Set.not_subset.mp source_subset with
      ⟨differenceEdge, source_mem, target_not_mem⟩
    exact ⟨{
      componentChange := componentChange
      step := step
      successor_eq := successor_eq
      pairClassification := pairClassification
      root_not_mem_selectedComponent := root_not_mem
      differenceEdge := differenceEdge
      membershipChange := Or.inl ⟨source_mem, target_not_mem⟩ }⟩

/-- The direct branch: the selected cross-pair component itself contains a
canonical-component symmetric-difference witness. -/
structure CompanionCrossPairDirectComponentContact
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  difference : CompanionCanonicalComponentDifference collar start
  differenceEdge_mem_selectedComponent :
    difference.differenceEdge ∈
      difference.componentChange.change.changeSource.coloring.kempeComponentSet
        (crossFaceZeroColor difference.step.firstHit.transfer.coordinate)
        difference.step.reentry.realization.companion
        difference.step.reentry.realization.component

/-- The remote branch: a canonical-component membership changes at an edge
outside the selected component, so its color is locally untouched. -/
structure CompanionCrossPairRemoteComponentReconnection
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  difference : CompanionCanonicalComponentDifference collar start
  differenceEdge_not_mem_selectedComponent :
    difference.differenceEdge ∉
      difference.componentChange.change.changeSource.coloring.kempeComponentSet
        (crossFaceZeroColor difference.step.firstHit.transfer.coordinate)
        difference.step.reentry.realization.companion
        difference.step.reentry.realization.component

/-- A concrete component change is either direct contact with the selected
cross-pair component or a remote reconnection at an untouched edge. -/
theorem CompanionCanonicalComponentDifference.directContact_or_remoteReconnection
    (difference : CompanionCanonicalComponentDifference collar start) :
    Nonempty (CompanionCrossPairDirectComponentContact collar start) ∨
      Nonempty (CompanionCrossPairRemoteComponentReconnection collar start) := by
  by_cases selected : difference.differenceEdge ∈
      difference.componentChange.change.changeSource.coloring.kempeComponentSet
        (crossFaceZeroColor difference.step.firstHit.transfer.coordinate)
        difference.step.reentry.realization.companion
        difference.step.reentry.realization.component
  · exact Or.inl ⟨{
      difference := difference
      differenceEdge_mem_selectedComponent := selected }⟩
  · exact Or.inr ⟨{
      difference := difference
      differenceEdge_not_mem_selectedComponent := selected }⟩

namespace CompanionCanonicalComponentDifference

variable (difference : CompanionCanonicalComponentDifference collar start)

/-- The lifted common-core edge rooting the return component. -/
def rootEdge :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).edgeSet :=
  collar.commonEdgeInSource
    difference.componentChange.returnData.lastOverlap.overlap.commonEdge

/-- The root carries the fixed outer color before the component-changing
transition. -/
theorem sourceRootColor_eq_breakOuter :
    difference.componentChange.change.changeSource.coloring
        difference.rootEdge =
      difference.componentChange.returnData.lastOverlap.overlap.breakOuterColor := by
  have color_eq :=
    difference.componentChange.returnData.suffixStateColor_eq_breakOuter
      difference.componentChange.change.reach_change
  simpa only [rootEdge,
    collar.sourceCommonColoring_apply_commonEdgeInSource] using color_eq

/-- Edge constancy preserves that outer root color across the changing
transition. -/
theorem targetRootColor_eq_breakOuter :
    difference.componentChange.change.changeTarget.coloring
        difference.rootEdge =
      difference.componentChange.returnData.lastOverlap.overlap.breakOuterColor := by
  have root_eq := difference.componentChange.change.changeTransition.2
  have source_eq_target :
      difference.componentChange.change.changeSource.coloring
          difference.rootEdge =
        difference.componentChange.change.changeTarget.coloring
          difference.rootEdge := by
    simpa only [rootEdge,
      collar.sourceCommonColoring_apply_commonEdgeInSource] using root_eq
  exact source_eq_target.symm.trans difference.sourceRootColor_eq_breakOuter

/-- The symmetric-difference witness is never the common root, which lies
in the canonical component on both sides. -/
theorem differenceEdge_ne_rootEdge :
    difference.differenceEdge ≠ difference.rootEdge := by
  have sourceRootSelected : difference.rootEdge ∈
      difference.componentChange.change.changeSource.coloring.bicoloredSet
        difference.componentChange.returnData.lastOverlap.overlap.fixedColor
        difference.componentChange.returnData.lastOverlap.overlap.breakOuterColor :=
    Or.inr difference.sourceRootColor_eq_breakOuter
  have targetRootSelected : difference.rootEdge ∈
      difference.componentChange.change.changeTarget.coloring.bicoloredSet
        difference.componentChange.returnData.lastOverlap.overlap.fixedColor
        difference.componentChange.returnData.lastOverlap.overlap.breakOuterColor :=
    Or.inr difference.targetRootColor_eq_breakOuter
  have sourceRootMem : difference.rootEdge ∈
      difference.componentChange.returnData.canonicalReturnComponentSet
        difference.componentChange.change.changeSource := by
    exact difference.componentChange.change.changeSource.coloring
      |>.mem_kempeComponentSetAtVertex_of_mem
        difference.componentChange.returnData.lastOverlap.overlap.fixedColor
        difference.componentChange.returnData.lastOverlap.overlap.breakOuterColor
        difference.rootEdge sourceRootSelected
  have targetRootMem : difference.rootEdge ∈
      difference.componentChange.returnData.canonicalReturnComponentSet
        difference.componentChange.change.changeTarget := by
    exact difference.componentChange.change.changeTarget.coloring
      |>.mem_kempeComponentSetAtVertex_of_mem
        difference.componentChange.returnData.lastOverlap.overlap.fixedColor
        difference.componentChange.returnData.lastOverlap.overlap.breakOuterColor
        difference.rootEdge targetRootSelected
  intro edge_eq
  rcases difference.membershipChange with sourceChange | targetChange
  · exact sourceChange.2 (edge_eq ▸ targetRootMem)
  · exact targetChange.1 (edge_eq ▸ sourceRootMem)

end CompanionCanonicalComponentDifference

namespace CompanionCrossPairDirectComponentContact

variable (contact : CompanionCrossPairDirectComponentContact collar start)

/-- Direct contact occurs in the source canonical component or the target
canonical component, according to the orientation of the set change. -/
theorem selectedComponent_meets_source_or_targetCanonicalComponent :
    (contact.difference.differenceEdge ∈
        contact.difference.componentChange.change.changeSource.coloring.kempeComponentSet
          (crossFaceZeroColor
            contact.difference.step.firstHit.transfer.coordinate)
          contact.difference.step.reentry.realization.companion
          contact.difference.step.reentry.realization.component ∧
      contact.difference.differenceEdge ∈
        contact.difference.componentChange.returnData.canonicalReturnComponentSet
          contact.difference.componentChange.change.changeSource) ∨
      (contact.difference.differenceEdge ∈
          contact.difference.componentChange.change.changeSource.coloring.kempeComponentSet
            (crossFaceZeroColor
              contact.difference.step.firstHit.transfer.coordinate)
            contact.difference.step.reentry.realization.companion
            contact.difference.step.reentry.realization.component ∧
        contact.difference.differenceEdge ∈
          contact.difference.componentChange.returnData.canonicalReturnComponentSet
            contact.difference.componentChange.change.changeTarget) := by
  rcases contact.difference.membershipChange with sourceChange | targetChange
  · exact Or.inl
      ⟨contact.differenceEdge_mem_selectedComponent, sourceChange.1⟩
  · exact Or.inr
      ⟨contact.differenceEdge_mem_selectedComponent, targetChange.2⟩

end CompanionCrossPairDirectComponentContact

namespace CompanionCrossPairRemoteComponentReconnection

variable (reconnection :
  CompanionCrossPairRemoteComponentReconnection collar start)

/-- At a remote reconnection witness, the component-changing swap preserves
the edge color exactly; only rooted connectivity membership changes. -/
theorem sourceColor_eq_targetColor :
    reconnection.difference.componentChange.change.changeSource.coloring
        reconnection.difference.differenceEdge =
      reconnection.difference.componentChange.change.changeTarget.coloring
        reconnection.difference.differenceEdge := by
  rw [← reconnection.difference.successor_eq,
    CompanionAdjacentEscapeStep.successor,
    reconnection.difference.step.reentry.coloring_eq,
    reconnection.difference.componentChange.change.changeSource.coloring
      |>.swapOnKempeComponent_apply_of_not_mem
        reconnection.differenceEdge_not_mem_selectedComponent]

/-- Although its canonical-component membership changes, a remote witness
belongs to the return-pair bicolored set in both endpoint colorings. -/
theorem differenceEdge_selected_in_source_and_target :
    reconnection.difference.differenceEdge ∈
        reconnection.difference.componentChange.change.changeSource.coloring.bicoloredSet
          reconnection.difference.componentChange.returnData.lastOverlap.overlap.fixedColor
          reconnection.difference.componentChange.returnData.lastOverlap.overlap.breakOuterColor ∧
      reconnection.difference.differenceEdge ∈
        reconnection.difference.componentChange.change.changeTarget.coloring.bicoloredSet
          reconnection.difference.componentChange.returnData.lastOverlap.overlap.fixedColor
          reconnection.difference.componentChange.returnData.lastOverlap.overlap.breakOuterColor := by
  let sourceColoring :=
    reconnection.difference.componentChange.change.changeSource.coloring
  let targetColoring :=
    reconnection.difference.componentChange.change.changeTarget.coloring
  let fixed :=
    reconnection.difference.componentChange.returnData.lastOverlap.overlap.fixedColor
  let outer :=
    reconnection.difference.componentChange.returnData.lastOverlap.overlap.breakOuterColor
  have color_eq : sourceColoring reconnection.difference.differenceEdge =
      targetColoring reconnection.difference.differenceEdge :=
    reconnection.sourceColor_eq_targetColor
  rcases reconnection.difference.membershipChange with
    sourceChange | targetChange
  · have sourceSelected := sourceColoring
      |>.mem_bicoloredSet_of_mem_kempeComponentSetAtVertex
        fixed outer reconnection.difference.rootEdge sourceChange.1
    have targetSelected : reconnection.difference.differenceEdge ∈
        targetColoring.bicoloredSet fixed outer := by
      rcases sourceSelected with selectedFixed | selectedOuter
      · exact Or.inl (color_eq.symm.trans selectedFixed)
      · exact Or.inr (color_eq.symm.trans selectedOuter)
    exact ⟨sourceSelected, targetSelected⟩
  · have targetSelected := targetColoring
      |>.mem_bicoloredSet_of_mem_kempeComponentSetAtVertex
        fixed outer reconnection.difference.rootEdge targetChange.2
    have sourceSelected : reconnection.difference.differenceEdge ∈
        sourceColoring.bicoloredSet fixed outer := by
      rcases targetSelected with selectedFixed | selectedOuter
      · exact Or.inl (color_eq.trans selectedFixed)
      · exact Or.inr (color_eq.trans selectedOuter)
    exact ⟨sourceSelected, targetSelected⟩

/-- Remote reconnection is an exact reachability flip between the same two
selected endpoint edges: one return-pair subgraph connects root to witness,
while the other does not. -/
theorem sourceReachable_not_targetReachable_or_reverse :
    let sourceColoring :=
      reconnection.difference.componentChange.change.changeSource.coloring
    let targetColoring :=
      reconnection.difference.componentChange.change.changeTarget.coloring
    let fixed :=
      reconnection.difference.componentChange.returnData.lastOverlap.overlap.fixedColor
    let outer :=
      reconnection.difference.componentChange.returnData.lastOverlap.overlap.breakOuterColor
    let root := reconnection.difference.rootEdge
    let witness := reconnection.difference.differenceEdge
    let sourceRootSelected : root ∈
        sourceColoring.bicoloredSet fixed outer :=
      Or.inr reconnection.difference.sourceRootColor_eq_breakOuter
    let targetRootSelected : root ∈
        targetColoring.bicoloredSet fixed outer :=
      Or.inr reconnection.difference.targetRootColor_eq_breakOuter
    let sourceWitnessSelected : witness ∈
        sourceColoring.bicoloredSet fixed outer :=
      reconnection.differenceEdge_selected_in_source_and_target.1
    let targetWitnessSelected : witness ∈
        targetColoring.bicoloredSet fixed outer :=
      reconnection.differenceEdge_selected_in_source_and_target.2
    ((sourceColoring.bicoloredSubgraph fixed outer).Reachable
          ⟨root, sourceRootSelected⟩ ⟨witness, sourceWitnessSelected⟩ ∧
        ¬(targetColoring.bicoloredSubgraph fixed outer).Reachable
          ⟨root, targetRootSelected⟩ ⟨witness, targetWitnessSelected⟩) ∨
      (¬(sourceColoring.bicoloredSubgraph fixed outer).Reachable
          ⟨root, sourceRootSelected⟩ ⟨witness, sourceWitnessSelected⟩ ∧
        (targetColoring.bicoloredSubgraph fixed outer).Reachable
          ⟨root, targetRootSelected⟩ ⟨witness, targetWitnessSelected⟩) := by
  dsimp only
  let sourceColoring :=
    reconnection.difference.componentChange.change.changeSource.coloring
  let targetColoring :=
    reconnection.difference.componentChange.change.changeTarget.coloring
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
  rcases reconnection.difference.membershipChange with
    sourceChange | targetChange
  · apply Or.inl
    constructor
    · exact (sourceColoring.mem_kempeComponentSetAtVertex_iff_reachable
        fixed outer root witness sourceRootSelected sourceWitnessSelected).1
          sourceChange.1
    · intro reachable
      exact sourceChange.2
        ((targetColoring.mem_kempeComponentSetAtVertex_iff_reachable
          fixed outer root witness targetRootSelected targetWitnessSelected).2
            reachable)
  · apply Or.inr
    constructor
    · intro reachable
      exact targetChange.1
        ((sourceColoring.mem_kempeComponentSetAtVertex_iff_reachable
          fixed outer root witness sourceRootSelected sourceWitnessSelected).2
            reachable)
    · exact (targetColoring.mem_kempeComponentSetAtVertex_iff_reachable
        fixed outer root witness targetRootSelected targetWitnessSelected).1
          targetChange.2

end CompanionCrossPairRemoteComponentReconnection

/-- The component-changing outcome of a closed circuit refines to direct
cross-pair contact or remote rooted-component reconnection. -/
theorem CompanionCanonicalSamePairComponentChange.directContact_or_remoteReconnection
    (componentChange :
      CompanionCanonicalSamePairComponentChange collar start) :
    Nonempty (CompanionCrossPairDirectComponentContact collar start) ∨
      Nonempty (CompanionCrossPairRemoteComponentReconnection collar start) := by
  rcases nonempty_companionCanonicalComponentDifference componentChange with
    ⟨difference⟩
  exact difference.directContact_or_remoteReconnection

/-- A closed companion circuit resolves into local cancellation, a concrete
cross-pair intersection, direct cross-pair contact, remote unchanged-color
reconnection, a shared-edge pivot, or full three-pair monodromy. -/
theorem closedCircuit_exists_localCancellation_or_crossPairIntersection_or_directContact_or_remoteReconnection_or_edgePivot_or_threePairMonodromy
    (closed : Relation.TransGen
      (CompanionAdjacentEscapeTransition collar) start start) :
    Nonempty (CompanionCanonicalComponentDisjointClosure collar start) ∨
      Nonempty (CompanionCanonicalComponentIntersection collar start) ∨
        Nonempty (CompanionCrossPairDirectComponentContact collar start) ∨
          Nonempty (CompanionCrossPairRemoteComponentReconnection
            collar start) ∨
            Nonempty (CompanionSameOuterTargetAvoidingEdgePivot collar start) ∨
              Nonempty (CompanionThreePairMonodromy collar start) := by
  rcases
      closedCircuit_exists_localCancellation_or_crossPairIntersection_or_componentChange_or_edgePivot_or_threePairMonodromy
        closed with hcancel | hintersection | hchange | hpivot | hmonodromy
  · exact Or.inl hcancel
  · exact Or.inr (Or.inl hintersection)
  · rcases hchange with ⟨componentChange⟩
    rcases componentChange.directContact_or_remoteReconnection with
      hcontact | hreconnection
    · exact Or.inr (Or.inr (Or.inl hcontact))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hreconnection)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpivot))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmonodromy))))

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
