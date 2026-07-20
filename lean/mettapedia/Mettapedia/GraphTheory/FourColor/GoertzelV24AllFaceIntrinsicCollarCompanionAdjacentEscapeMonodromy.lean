import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeOverlap

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

/-- The last break of a predicate along a finite chain retains a suffix on
which every subsequent target state still violates the predicate. -/
theorem reflTransGen_exists_last_predicate_break
    {State : Type*} {relation : State → State → Prop}
    {start finish : State} (predicate : State → Prop)
    (reachable : Relation.ReflTransGen relation start finish)
    (atStart : predicate start) (notAtFinish : ¬predicate finish) :
    ∃ before after,
      Relation.ReflTransGen relation start before ∧
        relation before after ∧ predicate before ∧ ¬predicate after ∧
        Relation.ReflTransGen
          (fun source target => relation source target ∧ ¬predicate target)
          after finish := by
  induction reachable with
  | refl => exact False.elim (notAtFinish atStart)
  | @tail middle finish reachable step ih =>
      by_cases atMiddle : predicate middle
      · exact ⟨middle, finish, reachable, step, atMiddle, notAtFinish,
          Relation.ReflTransGen.refl⟩
      · rcases ih atMiddle with
          ⟨before, after, hprefix, hbreak, hbefore, hafter, hsuffix⟩
        exact ⟨before, after, hprefix, hbreak, hbefore, hafter,
          hsuffix.tail ⟨step, notAtFinish⟩⟩

/-- A finite chain either satisfies a stepwise condition throughout or
retains one exact transition where the condition fails, together with both
remaining path segments. -/
theorem reflTransGen_lift_condition_or_exists_failure
    {State : Type*} {relation : State → State → Prop}
    {start finish : State} (condition : State → State → Prop)
    (reachable : Relation.ReflTransGen relation start finish) :
    Relation.ReflTransGen
        (fun source target =>
          relation source target ∧ condition source target)
        start finish ∨
      ∃ before after,
        Relation.ReflTransGen relation start before ∧
          relation before after ∧ ¬condition before after ∧
          Relation.ReflTransGen relation after finish := by
  induction reachable with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail middle finish reachable step ih =>
      rcases ih with hall | ⟨before, after, hprefix, hfailure,
        hnot, hsuffix⟩
      · by_cases holds : condition middle finish
        · exact Or.inl (hall.tail ⟨step, holds⟩)
        · exact Or.inr ⟨middle, finish,
            Relation.ReflTransGen.mono (fun _ _ retained => retained.1) hall,
            step, holds, Relation.ReflTransGen.refl⟩
      · exact Or.inr ⟨before, after, hprefix, hfailure, hnot,
          hsuffix.tail step⟩

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

namespace CompanionAdjacentEscapeStep

variable {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}
  (step : CompanionAdjacentEscapeStep collar sourceEscape)

/-- If a provenance-retaining transition leaves a common-core edge color
unchanged, its selected component avoids that lifted edge. -/
theorem commonEdge_not_mem_component_of_unchanged
    (edge : collar.commonCore.edgeSet)
    (unchanged : collar.sourceCommonColoring sourceEscape edge =
      collar.sourceCommonColoring step.successor edge) :
    collar.commonEdgeInSource edge ∉
      sourceEscape.coloring.kempeComponentSet
        (crossFaceZeroColor step.firstHit.transfer.coordinate)
        step.reentry.realization.companion
        step.reentry.realization.component := by
  intro member
  rcases step.commonEdge_color_orientation edge member with
    ⟨hsource, hsuccessor⟩ | ⟨hsource, hsuccessor⟩
  · exact step.distinguished_ne_companion
      (hsource.symm.trans (unchanged.trans hsuccessor))
  · exact step.distinguished_ne_companion
      (hsuccessor.symm.trans (unchanged.symm.trans hsource))

end CompanionAdjacentEscapeStep

namespace CompanionRepairBreakOverlap

variable {start : sourceNormal.KempeOrbitAdjacentEscape}
  (overlap : CompanionRepairBreakOverlap collar start)

/-- Equal outer colors make the repair and break selections the same
unordered nonzero color pair. -/
theorem repairPair_eq_breakPair_of_sameOuter
    (sameOuter : overlap.repairOuterColor = overlap.breakOuterColor) :
    ({crossFaceZeroColor
          overlap.repairStep.firstHit.transfer.coordinate,
        overlap.repairStep.reentry.realization.companion} : Set Color) =
      {crossFaceZeroColor
          overlap.breakStep.firstHit.transfer.coordinate,
        overlap.breakStep.reentry.realization.companion} := by
  rcases overlap.repairPair_orientation with hrepair | hrepair <;>
    rcases overlap.breakPair_orientation with hbreak | hbreak
  all_goals
    ext color
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop

end CompanionRepairBreakOverlap

/-- A repair--break overlap whose break is chosen last, so the retained
suffix never returns to the fixed target color at the shared edge. -/
structure CompanionLastRepairBreakOverlap
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  overlap : CompanionRepairBreakOverlap collar start
  suffix_avoids_target : Relation.ReflTransGen
    (fun source target =>
      CompanionAdjacentEscapeTransition collar source target ∧
        collar.sourceCommonColoring target overlap.commonEdge ≠
          collar.targetCommonColoring overlap.commonEdge)
    overlap.breakTarget overlap.repairSource

namespace CompanionLastRepairBreakOverlap

variable {start : sourceNormal.KempeOrbitAdjacentEscape}
  (lastOverlap : CompanionLastRepairBreakOverlap collar start)

/-- The restricted suffix projects to the ordinary companion transition
relation. -/
theorem suffix_reachable : Relation.ReflTransGen
    (CompanionAdjacentEscapeTransition collar)
    lastOverlap.overlap.breakTarget lastOverlap.overlap.repairSource := by
  exact Relation.ReflTransGen.mono (fun _ _ step => step.1)
    lastOverlap.suffix_avoids_target

/-- Every state reached along the retained suffix still differs from the
fixed target color at the shared edge. -/
theorem suffixState_ne_target
    {state : sourceNormal.KempeOrbitAdjacentEscape}
    (reachable : Relation.ReflTransGen
      (fun source target =>
        CompanionAdjacentEscapeTransition collar source target ∧
          collar.sourceCommonColoring target
              lastOverlap.overlap.commonEdge ≠
            collar.targetCommonColoring lastOverlap.overlap.commonEdge)
      lastOverlap.overlap.breakTarget state) :
    collar.sourceCommonColoring state lastOverlap.overlap.commonEdge ≠
      collar.targetCommonColoring lastOverlap.overlap.commonEdge := by
  induction reachable with
  | refl => exact lastOverlap.overlap.breakTarget_ne_target
  | tail _ step _ => exact step.2

/-- In the three-color branch, the two outer colors are genuinely
different. -/
theorem breakOuterColor_ne_repairOuterColor
    (threeColorTurn :
      lastOverlap.overlap.breakOuterColor =
        lastOverlap.overlap.fixedColor +
          lastOverlap.overlap.repairOuterColor) :
    lastOverlap.overlap.breakOuterColor ≠
      lastOverlap.overlap.repairOuterColor := by
  intro heq
  exact add_ne_right_of_ne_zero lastOverlap.overlap.fixedColor_ne_zero
    (threeColorTurn.symm.trans heq)

end CompanionLastRepairBreakOverlap

/-- Every closed companion circuit admits a last-break overlap with a
target-avoiding suffix. -/
theorem nonempty_companionLastRepairBreakOverlap_of_closedCircuit
    {start : sourceNormal.KempeOrbitAdjacentEscape}
    (closed : Relation.TransGen
      (CompanionAdjacentEscapeTransition collar) start start) :
    Nonempty (CompanionLastRepairBreakOverlap collar start) := by
  rcases (Relation.transGen_iff
      (CompanionAdjacentEscapeTransition collar) start start).1 closed with
    hself | ⟨repairSource, hprefix, hrepair⟩
  · exact False.elim (hself.ne rfl)
  · rcases hrepair.exists_repairedCommonEdge with
      ⟨edge, hrepairSource, hstart⟩
    let predicate := fun escape : sourceNormal.KempeOrbitAdjacentEscape =>
      collar.sourceCommonColoring escape edge =
        collar.targetCommonColoring edge
    rcases reflTransGen_exists_last_predicate_break predicate
        hprefix.to_reflTransGen hstart hrepairSource with
      ⟨breakSource, breakTarget, hbreakReach, hbreak,
        hbefore, hafter, hrestrictedSuffix⟩
    rcases hrepair with ⟨repairStep, hrepairSuccessor⟩
    rcases hbreak with ⟨breakStep, hbreakSuccessor⟩
    let overlap : CompanionRepairBreakOverlap collar start := {
      repairSource := repairSource
      commonEdge := edge
      breakSource := breakSource
      breakTarget := breakTarget
      repairStep := repairStep
      repair_successor_eq := hrepairSuccessor
      breakStep := breakStep
      break_successor_eq := hbreakSuccessor
      reach_repair := hprefix
      reach_break := hbreakReach
      reach_repair_after_break :=
        Relation.ReflTransGen.mono (fun _ _ step => step.1)
          hrestrictedSuffix
      repairSource_ne_target := hrepairSource
      start_eq_target := hstart
      breakSource_eq_target := hbefore
      breakTarget_ne_target := hafter }
    exact ⟨{
      overlap := overlap
      suffix_avoids_target := by
        simpa only [overlap, predicate] using hrestrictedSuffix }⟩

/-- A target-avoiding suffix all of whose transitions preserve the shared
edge color. -/
structure CompanionTargetAvoidingEdgeConstantSuffix
    {start : sourceNormal.KempeOrbitAdjacentEscape}
    (lastOverlap : CompanionLastRepairBreakOverlap collar start) where
  path : Relation.ReflTransGen
    (fun source target =>
      (CompanionAdjacentEscapeTransition collar source target ∧
        collar.sourceCommonColoring target
              lastOverlap.overlap.commonEdge ≠
          collar.targetCommonColoring lastOverlap.overlap.commonEdge) ∧
        collar.sourceCommonColoring source
              lastOverlap.overlap.commonEdge =
          collar.sourceCommonColoring target
            lastOverlap.overlap.commonEdge)
    lastOverlap.overlap.breakTarget lastOverlap.overlap.repairSource

namespace CompanionTargetAvoidingEdgeConstantSuffix

variable {start : sourceNormal.KempeOrbitAdjacentEscape}
  {lastOverlap : CompanionLastRepairBreakOverlap collar start}
  (constantSuffix : CompanionTargetAvoidingEdgeConstantSuffix lastOverlap)

/-- Every retained transition of an edge-constant suffix has a selected
component avoiding the shared lifted edge. -/
theorem transition_exists_component_avoiding_edge
    {source target : sourceNormal.KempeOrbitAdjacentEscape}
    (retained :
      (CompanionAdjacentEscapeTransition collar source target ∧
        collar.sourceCommonColoring target
              lastOverlap.overlap.commonEdge ≠
          collar.targetCommonColoring lastOverlap.overlap.commonEdge) ∧
        collar.sourceCommonColoring source
              lastOverlap.overlap.commonEdge =
          collar.sourceCommonColoring target
            lastOverlap.overlap.commonEdge) :
    ∃ step : CompanionAdjacentEscapeStep collar source,
      step.successor = target ∧
        collar.commonEdgeInSource lastOverlap.overlap.commonEdge ∉
          source.coloring.kempeComponentSet
            (crossFaceZeroColor step.firstHit.transfer.coordinate)
            step.reentry.realization.companion
            step.reentry.realization.component := by
  rcases retained.1.1 with ⟨step, hsuccessor⟩
  refine ⟨step, hsuccessor, ?_⟩
  apply step.commonEdge_not_mem_component_of_unchanged
  rw [hsuccessor]
  exact retained.2

end CompanionTargetAvoidingEdgeConstantSuffix

/-- One exact target-avoiding suffix transition which changes the shared
edge, retaining its component realization and both path segments. -/
structure CompanionTargetAvoidingEdgePivot
    {start : sourceNormal.KempeOrbitAdjacentEscape}
    (lastOverlap : CompanionLastRepairBreakOverlap collar start) where
  pivotSource : sourceNormal.KempeOrbitAdjacentEscape
  pivotTarget : sourceNormal.KempeOrbitAdjacentEscape
  pivotStep : CompanionAdjacentEscapeStep collar pivotSource
  pivot_successor_eq : pivotStep.successor = pivotTarget
  reach_pivot : Relation.ReflTransGen
    (fun source target =>
      CompanionAdjacentEscapeTransition collar source target ∧
        collar.sourceCommonColoring target
              lastOverlap.overlap.commonEdge ≠
          collar.targetCommonColoring lastOverlap.overlap.commonEdge)
    lastOverlap.overlap.breakTarget pivotSource
  reach_repair_after_pivot : Relation.ReflTransGen
    (fun source target =>
      CompanionAdjacentEscapeTransition collar source target ∧
        collar.sourceCommonColoring target
              lastOverlap.overlap.commonEdge ≠
          collar.targetCommonColoring lastOverlap.overlap.commonEdge)
    pivotTarget lastOverlap.overlap.repairSource
  sourceColor_ne_target :
    collar.sourceCommonColoring pivotSource
        lastOverlap.overlap.commonEdge ≠
      collar.targetCommonColoring lastOverlap.overlap.commonEdge
  targetColor_ne_target :
    collar.sourceCommonColoring pivotTarget
        lastOverlap.overlap.commonEdge ≠
      collar.targetCommonColoring lastOverlap.overlap.commonEdge
  sourceColor_ne_targetColor :
    collar.sourceCommonColoring pivotSource
        lastOverlap.overlap.commonEdge ≠
      collar.sourceCommonColoring pivotTarget
        lastOverlap.overlap.commonEdge

namespace CompanionTargetAvoidingEdgePivot

variable {start : sourceNormal.KempeOrbitAdjacentEscape}
  {lastOverlap : CompanionLastRepairBreakOverlap collar start}
  (pivot : CompanionTargetAvoidingEdgePivot lastOverlap)

/-- A target-avoiding edge pivot uses a component containing the shared
lifted edge. -/
theorem pivotEdge_mem_component :
    collar.commonEdgeInSource lastOverlap.overlap.commonEdge ∈
      pivot.pivotSource.coloring.kempeComponentSet
        (crossFaceZeroColor pivot.pivotStep.firstHit.transfer.coordinate)
        pivot.pivotStep.reentry.realization.companion
        pivot.pivotStep.reentry.realization.component := by
  apply pivot.pivotStep.changedCommonEdge_mem_component
  rw [pivot.pivot_successor_eq]
  exact pivot.sourceColor_ne_targetColor

/-- The target-avoiding pivot's selected pair is exactly its two distinct
before/after colors at the shared edge. -/
theorem pivotPair_orientation :
    (collar.sourceCommonColoring pivot.pivotSource
            lastOverlap.overlap.commonEdge =
          crossFaceZeroColor pivot.pivotStep.firstHit.transfer.coordinate ∧
        collar.sourceCommonColoring pivot.pivotTarget
            lastOverlap.overlap.commonEdge =
          pivot.pivotStep.reentry.realization.companion) ∨
      (collar.sourceCommonColoring pivot.pivotSource
            lastOverlap.overlap.commonEdge =
          pivot.pivotStep.reentry.realization.companion ∧
        collar.sourceCommonColoring pivot.pivotTarget
            lastOverlap.overlap.commonEdge =
          crossFaceZeroColor
            pivot.pivotStep.firstHit.transfer.coordinate) := by
  simpa only [pivot.pivot_successor_eq] using
    pivot.pivotStep.commonEdge_color_orientation
      lastOverlap.overlap.commonEdge pivot.pivotEdge_mem_component

end CompanionTargetAvoidingEdgePivot

/-- A target-avoiding suffix either preserves the shared edge at every
step or contains an actual component-realized edge pivot. -/
theorem CompanionLastRepairBreakOverlap.edgeConstantSuffix_or_edgePivot
    {start : sourceNormal.KempeOrbitAdjacentEscape}
    (lastOverlap : CompanionLastRepairBreakOverlap collar start) :
    Nonempty (CompanionTargetAvoidingEdgeConstantSuffix lastOverlap) ∨
      Nonempty (CompanionTargetAvoidingEdgePivot lastOverlap) := by
  let condition := fun source target :
      sourceNormal.KempeOrbitAdjacentEscape =>
    collar.sourceCommonColoring source lastOverlap.overlap.commonEdge =
      collar.sourceCommonColoring target lastOverlap.overlap.commonEdge
  rcases reflTransGen_lift_condition_or_exists_failure condition
      lastOverlap.suffix_avoids_target with
    hall | ⟨pivotSource, pivotTarget, hprefix, hpivot, hchanged, hsuffix⟩
  · exact Or.inl ⟨{
      path := by simpa only [condition] using hall }⟩
  · have hsourceNeTarget := lastOverlap.suffixState_ne_target hprefix
    rcases hpivot.1 with ⟨pivotStep, hpivotSuccessor⟩
    exact Or.inr ⟨{
      pivotSource := pivotSource
      pivotTarget := pivotTarget
      pivotStep := pivotStep
      pivot_successor_eq := hpivotSuccessor
      reach_pivot := hprefix
      reach_repair_after_pivot := hsuffix
      sourceColor_ne_target := hsourceNeTarget
      targetColor_ne_target := hpivot.2
      sourceColor_ne_targetColor := hchanged }⟩

/-- The component-realized pivot forced inside a target-avoiding suffix
whose two endpoint outer colors differ. -/
structure CompanionTargetAvoidingThreeColorPivot
    {start : sourceNormal.KempeOrbitAdjacentEscape}
    (lastOverlap : CompanionLastRepairBreakOverlap collar start) where
  pivotSource : sourceNormal.KempeOrbitAdjacentEscape
  pivotTarget : sourceNormal.KempeOrbitAdjacentEscape
  pivotStep : CompanionAdjacentEscapeStep collar pivotSource
  pivot_successor_eq : pivotStep.successor = pivotTarget
  reach_pivot : Relation.ReflTransGen
    (fun source target =>
      CompanionAdjacentEscapeTransition collar source target ∧
        collar.sourceCommonColoring target
              lastOverlap.overlap.commonEdge ≠
          collar.targetCommonColoring lastOverlap.overlap.commonEdge)
    lastOverlap.overlap.breakTarget pivotSource
  reach_repair_after_pivot : Relation.ReflTransGen
    (fun source target =>
      CompanionAdjacentEscapeTransition collar source target ∧
        collar.sourceCommonColoring target
              lastOverlap.overlap.commonEdge ≠
          collar.targetCommonColoring lastOverlap.overlap.commonEdge)
    pivotTarget lastOverlap.overlap.repairSource
  sourceColor_eq_breakOuter :
    collar.sourceCommonColoring pivotSource
        lastOverlap.overlap.commonEdge =
      lastOverlap.overlap.breakOuterColor
  targetColor_eq_repairOuter :
    collar.sourceCommonColoring pivotTarget
        lastOverlap.overlap.commonEdge =
      lastOverlap.overlap.repairOuterColor
  threeColorTurn :
    lastOverlap.overlap.breakOuterColor =
      lastOverlap.overlap.fixedColor +
        lastOverlap.overlap.repairOuterColor

namespace CompanionTargetAvoidingThreeColorPivot

variable {start : sourceNormal.KempeOrbitAdjacentEscape}
  {lastOverlap : CompanionLastRepairBreakOverlap collar start}
  (pivot : CompanionTargetAvoidingThreeColorPivot lastOverlap)

/-- The forced middle pivot component contains the same lifted common-core
edge as the enclosing break and repair components. -/
theorem pivotEdge_mem_component :
    collar.commonEdgeInSource lastOverlap.overlap.commonEdge ∈
      pivot.pivotSource.coloring.kempeComponentSet
        (crossFaceZeroColor pivot.pivotStep.firstHit.transfer.coordinate)
        pivot.pivotStep.reentry.realization.companion
        pivot.pivotStep.reentry.realization.component := by
  apply pivot.pivotStep.changedCommonEdge_mem_component
  rw [pivot.pivot_successor_eq, pivot.sourceColor_eq_breakOuter,
    pivot.targetColor_eq_repairOuter]
  exact lastOverlap.breakOuterColor_ne_repairOuterColor pivot.threeColorTurn

/-- The middle component uses exactly the two nonfixed outer colors at the
shared edge. -/
theorem pivotPair_orientation :
    (lastOverlap.overlap.breakOuterColor =
          crossFaceZeroColor pivot.pivotStep.firstHit.transfer.coordinate ∧
        lastOverlap.overlap.repairOuterColor =
          pivot.pivotStep.reentry.realization.companion) ∨
      (lastOverlap.overlap.breakOuterColor =
          pivot.pivotStep.reentry.realization.companion ∧
        lastOverlap.overlap.repairOuterColor =
          crossFaceZeroColor
            pivot.pivotStep.firstHit.transfer.coordinate) := by
  simpa only [pivot.sourceColor_eq_breakOuter,
      pivot.pivot_successor_eq, pivot.targetColor_eq_repairOuter] using
    pivot.pivotStep.commonEdge_color_orientation
      lastOverlap.overlap.commonEdge pivot.pivotEdge_mem_component

end CompanionTargetAvoidingThreeColorPivot

/-- A three-color last-break overlap forces an actual middle Kempe
component on the remaining nonfixed color pair. -/
theorem CompanionLastRepairBreakOverlap.nonempty_threeColorPivot
    {start : sourceNormal.KempeOrbitAdjacentEscape}
    (lastOverlap : CompanionLastRepairBreakOverlap collar start)
    (threeColorTurn :
      lastOverlap.overlap.breakOuterColor =
        lastOverlap.overlap.fixedColor +
          lastOverlap.overlap.repairOuterColor) :
    Nonempty (CompanionTargetAvoidingThreeColorPivot lastOverlap) := by
  let predicate := fun escape : sourceNormal.KempeOrbitAdjacentEscape =>
    collar.sourceCommonColoring escape lastOverlap.overlap.commonEdge =
      lastOverlap.overlap.breakOuterColor
  have hatStart : predicate lastOverlap.overlap.breakTarget := rfl
  have hnotAtFinish : ¬predicate lastOverlap.overlap.repairSource := by
    intro heq
    apply Ne.symm
      (lastOverlap.breakOuterColor_ne_repairOuterColor threeColorTurn)
    simpa only [predicate, CompanionRepairBreakOverlap.repairOuterColor] using
      heq
  rcases reflTransGen_exists_predicate_break_with_suffix predicate
      lastOverlap.suffix_avoids_target hatStart hnotAtFinish with
    ⟨pivotSource, pivotTarget, hprefix, hpivot, hsuffix,
      hsource, htarget⟩
  have hpivotTargetNeFixed :
      collar.sourceCommonColoring pivotTarget
          lastOverlap.overlap.commonEdge ≠
        collar.targetCommonColoring lastOverlap.overlap.commonEdge :=
    hpivot.2
  have hpivotTargetNeZero :
      collar.sourceCommonColoring pivotTarget
          lastOverlap.overlap.commonEdge ≠ 0 := by
    rw [collar.sourceCommonColoring_apply_commonEdgeInSource]
    exact pivotTarget.isTait _
  have hpivotTargetEqRepair :
      collar.sourceCommonColoring pivotTarget
          lastOverlap.overlap.commonEdge =
        lastOverlap.overlap.repairOuterColor := by
    by_contra hpivotTargetNeRepair
    exact false_of_four_pairwise_distinct_nonzero_colors
      lastOverlap.overlap.fixedColor_ne_zero
      lastOverlap.overlap.breakOuterColor_ne_zero
      lastOverlap.overlap.repairOuterColor_ne_zero
      hpivotTargetNeZero
      lastOverlap.overlap.breakOuterColor_ne_fixedColor.symm
      lastOverlap.overlap.repairOuterColor_ne_fixedColor.symm
      (Ne.symm hpivotTargetNeFixed)
      (lastOverlap.breakOuterColor_ne_repairOuterColor threeColorTurn)
      (Ne.symm htarget)
      (Ne.symm hpivotTargetNeRepair)
  rcases hpivot.1 with ⟨pivotStep, hpivotSuccessor⟩
  exact ⟨{
    pivotSource := pivotSource
    pivotTarget := pivotTarget
    pivotStep := pivotStep
    pivot_successor_eq := hpivotSuccessor
    reach_pivot := hprefix
    reach_repair_after_pivot := hsuffix
    sourceColor_eq_breakOuter := hsource
    targetColor_eq_repairOuter := hpivotTargetEqRepair
    threeColorTurn := threeColorTurn }⟩

/-- The three component-realized color-pair actions forced by a nontrivial
target-avoiding monodromy: fixed/break, break/repair, and repair/fixed. -/
structure CompanionThreePairMonodromy
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  lastOverlap : CompanionLastRepairBreakOverlap collar start
  pivot : CompanionTargetAvoidingThreeColorPivot lastOverlap

namespace CompanionThreePairMonodromy

variable {start : sourceNormal.KempeOrbitAdjacentEscape}
  (monodromy : CompanionThreePairMonodromy collar start)

/-- The three local colors in the monodromy are pairwise distinct. -/
theorem colors_pairwise_distinct :
    monodromy.lastOverlap.overlap.fixedColor ≠
        monodromy.lastOverlap.overlap.breakOuterColor ∧
      monodromy.lastOverlap.overlap.fixedColor ≠
        monodromy.lastOverlap.overlap.repairOuterColor ∧
      monodromy.lastOverlap.overlap.breakOuterColor ≠
        monodromy.lastOverlap.overlap.repairOuterColor :=
  ⟨monodromy.lastOverlap.overlap.breakOuterColor_ne_fixedColor.symm,
    monodromy.lastOverlap.overlap.repairOuterColor_ne_fixedColor.symm,
    monodromy.lastOverlap.breakOuterColor_ne_repairOuterColor
      monodromy.pivot.threeColorTurn⟩

end CompanionThreePairMonodromy

/-- The only unresolved closed-circuit branch after retaining last-break
monodromy is a same-outer-color return.  Every different-outer branch
contains the full three-pair component cycle. -/
theorem closedCircuit_exists_sameOuterLastOverlap_or_threePairMonodromy
    {start : sourceNormal.KempeOrbitAdjacentEscape}
    (closed : Relation.TransGen
      (CompanionAdjacentEscapeTransition collar) start start) :
    (∃ lastOverlap : CompanionLastRepairBreakOverlap collar start,
        lastOverlap.overlap.repairOuterColor =
          lastOverlap.overlap.breakOuterColor) ∨
      Nonempty (CompanionThreePairMonodromy collar start) := by
  rcases nonempty_companionLastRepairBreakOverlap_of_closedCircuit closed with
    ⟨lastOverlap⟩
  rcases lastOverlap.overlap
      |>.repairOuterColor_eq_breakOuterColor_or_threeColorTurn with
    hsame | hturn
  · exact Or.inl ⟨lastOverlap, hsame⟩
  · rcases lastOverlap.nonempty_threeColorPivot hturn with ⟨pivot⟩
    exact Or.inr ⟨{
      lastOverlap := lastOverlap
      pivot := pivot }⟩

/-- The residual same-outer branch in which every intervening selected
component avoids the shared edge. -/
structure CompanionSameOuterEdgeConstantReturn
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  lastOverlap : CompanionLastRepairBreakOverlap collar start
  sameOuter : lastOverlap.overlap.repairOuterColor =
    lastOverlap.overlap.breakOuterColor
  constantSuffix :
    CompanionTargetAvoidingEdgeConstantSuffix lastOverlap

/-- The same-outer branch in which the target-avoiding suffix itself
contains a component-realized pivot on the shared edge. -/
structure CompanionSameOuterTargetAvoidingEdgePivot
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  lastOverlap : CompanionLastRepairBreakOverlap collar start
  sameOuter : lastOverlap.overlap.repairOuterColor =
    lastOverlap.overlap.breakOuterColor
  pivot : CompanionTargetAvoidingEdgePivot lastOverlap

/-- Closed companion recurrence has exactly three structural outcomes:
an edge-constant same-pair return, a nonfixed shared-edge pivot inside that
return, or the full three-pair monodromy. -/
theorem closedCircuit_exists_sameOuterEdgeConstantReturn_or_edgePivot_or_threePairMonodromy
    {start : sourceNormal.KempeOrbitAdjacentEscape}
    (closed : Relation.TransGen
      (CompanionAdjacentEscapeTransition collar) start start) :
    Nonempty (CompanionSameOuterEdgeConstantReturn collar start) ∨
      Nonempty (CompanionSameOuterTargetAvoidingEdgePivot collar start) ∨
        Nonempty (CompanionThreePairMonodromy collar start) := by
  rcases closedCircuit_exists_sameOuterLastOverlap_or_threePairMonodromy
      closed with ⟨lastOverlap, hsame⟩ | hmonodromy
  · rcases lastOverlap.edgeConstantSuffix_or_edgePivot with
      hconstant | hpivot
    · rcases hconstant with ⟨constantSuffix⟩
      exact Or.inl ⟨{
        lastOverlap := lastOverlap
        sameOuter := hsame
        constantSuffix := constantSuffix }⟩
    · rcases hpivot with ⟨pivot⟩
      exact Or.inr (Or.inl ⟨{
        lastOverlap := lastOverlap
        sameOuter := hsame
        pivot := pivot }⟩)
  · exact Or.inr (Or.inr hmonodromy)

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
