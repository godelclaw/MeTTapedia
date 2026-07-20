import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeCircuit
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeSwitchSquare

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

/-- A predicate break on a finite transition chain retains both the prefix
to the breaking transition and the suffix from it to the endpoint. -/
theorem reflTransGen_exists_predicate_break_with_suffix
    {State : Type*} {relation : State → State → Prop}
    {start finish : State} (predicate : State → Prop)
    (reachable : Relation.ReflTransGen relation start finish)
    (atStart : predicate start) (notAtFinish : ¬predicate finish) :
    ∃ before after,
      Relation.ReflTransGen relation start before ∧
        relation before after ∧
        Relation.ReflTransGen relation after finish ∧
        predicate before ∧ ¬predicate after := by
  induction reachable with
  | refl => exact False.elim (notAtFinish atStart)
  | @tail middle finish reachable step ih =>
      by_cases atMiddle : predicate middle
      · exact ⟨middle, finish, reachable, step,
          Relation.ReflTransGen.refl, atMiddle, notAtFinish⟩
      · rcases ih atMiddle with
          ⟨before, after, hprefix, hbreak, hsuffix, hbefore, hafter⟩
        exact ⟨before, after, hprefix, hbreak, hsuffix.tail step,
          hbefore, hafter⟩

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

namespace CompanionAdjacentEscapeStep

variable (step : CompanionAdjacentEscapeStep collar sourceEscape)

/-- If a common-core edge changes under a provenance-retaining step, its
source-deletion image belongs to the retained Kempe component. -/
theorem changedCommonEdge_mem_component
    (edge : collar.commonCore.edgeSet)
    (changed : collar.sourceCommonColoring sourceEscape edge ≠
      collar.sourceCommonColoring step.successor edge) :
    collar.commonEdgeInSource edge ∈
      sourceEscape.coloring.kempeComponentSet
        (crossFaceZeroColor step.firstHit.transfer.coordinate)
        step.reentry.realization.companion
        step.reentry.realization.component := by
  by_contra hnot
  apply changed
  rw [collar.sourceCommonColoring_apply_commonEdgeInSource,
    collar.sourceCommonColoring_apply_commonEdgeInSource,
    successor, step.reentry.coloring_eq,
    sourceEscape.coloring.swapOnKempeComponent_apply_of_not_mem hnot]

/-- On an edge in the retained component, the source and successor colors
are exactly the two selected colors in opposite order. -/
theorem commonEdge_color_orientation
    (edge : collar.commonCore.edgeSet)
    (member : collar.commonEdgeInSource edge ∈
      sourceEscape.coloring.kempeComponentSet
        (crossFaceZeroColor step.firstHit.transfer.coordinate)
        step.reentry.realization.companion
        step.reentry.realization.component) :
    (collar.sourceCommonColoring sourceEscape edge =
          crossFaceZeroColor step.firstHit.transfer.coordinate ∧
        collar.sourceCommonColoring step.successor edge =
          step.reentry.realization.companion) ∨
      (collar.sourceCommonColoring sourceEscape edge =
          step.reentry.realization.companion ∧
        collar.sourceCommonColoring step.successor edge =
          crossFaceZeroColor step.firstHit.transfer.coordinate) := by
  rcases sourceEscape.coloring.mem_bicoloredSet_of_mem_kempeComponentSet
      member with hdistinguished | hcompanion
  · apply Or.inl
    constructor
    · simpa only [collar.sourceCommonColoring_apply_commonEdgeInSource] using
        hdistinguished
    · rw [collar.sourceCommonColoring_apply_commonEdgeInSource,
        successor, step.reentry.coloring_eq,
        sourceEscape.coloring.swapOnKempeComponent_apply_of_mem member,
        hdistinguished, Equiv.swap_apply_left]
  · apply Or.inr
    constructor
    · simpa only [collar.sourceCommonColoring_apply_commonEdgeInSource] using
        hcompanion
    · rw [collar.sourceCommonColoring_apply_commonEdgeInSource,
        successor, step.reentry.coloring_eq,
        sourceEscape.coloring.swapOnKempeComponent_apply_of_mem member,
        hcompanion, Equiv.swap_apply_right]

end CompanionAdjacentEscapeStep

/-- The exact two component-realized transitions surrounding one shared
common-core edge in a closed companion circuit.  The break occurs on the
retained prefix and its suffix leads to the final repair. -/
structure CompanionRepairBreakOverlap
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  repairSource : sourceNormal.KempeOrbitAdjacentEscape
  commonEdge : collar.commonCore.edgeSet
  breakSource : sourceNormal.KempeOrbitAdjacentEscape
  breakTarget : sourceNormal.KempeOrbitAdjacentEscape
  repairStep : CompanionAdjacentEscapeStep collar repairSource
  repair_successor_eq : repairStep.successor = start
  breakStep : CompanionAdjacentEscapeStep collar breakSource
  break_successor_eq : breakStep.successor = breakTarget
  reach_repair : Relation.TransGen
    (CompanionAdjacentEscapeTransition collar) start repairSource
  reach_break : Relation.ReflTransGen
    (CompanionAdjacentEscapeTransition collar) start breakSource
  reach_repair_after_break : Relation.ReflTransGen
    (CompanionAdjacentEscapeTransition collar) breakTarget repairSource
  repairSource_ne_target :
    collar.sourceCommonColoring repairSource commonEdge ≠
      collar.targetCommonColoring commonEdge
  start_eq_target :
    collar.sourceCommonColoring start commonEdge =
      collar.targetCommonColoring commonEdge
  breakSource_eq_target :
    collar.sourceCommonColoring breakSource commonEdge =
      collar.targetCommonColoring commonEdge
  breakTarget_ne_target :
    collar.sourceCommonColoring breakTarget commonEdge ≠
      collar.targetCommonColoring commonEdge

namespace CompanionRepairBreakOverlap

variable {start : sourceNormal.KempeOrbitAdjacentEscape}
  (overlap : CompanionRepairBreakOverlap collar start)

/-- The final repair component contains the shared common-core edge. -/
theorem repairEdge_mem_component :
    collar.commonEdgeInSource overlap.commonEdge ∈
      overlap.repairSource.coloring.kempeComponentSet
        (crossFaceZeroColor overlap.repairStep.firstHit.transfer.coordinate)
        overlap.repairStep.reentry.realization.companion
        overlap.repairStep.reentry.realization.component := by
  apply overlap.repairStep.changedCommonEdge_mem_component
  rw [overlap.repair_successor_eq]
  intro heq
  exact overlap.repairSource_ne_target
    (heq.trans overlap.start_eq_target)

/-- The earlier breaking component contains the same common-core edge. -/
theorem breakEdge_mem_component :
    collar.commonEdgeInSource overlap.commonEdge ∈
      overlap.breakSource.coloring.kempeComponentSet
        (crossFaceZeroColor overlap.breakStep.firstHit.transfer.coordinate)
        overlap.breakStep.reentry.realization.companion
        overlap.breakStep.reentry.realization.component := by
  apply overlap.breakStep.changedCommonEdge_mem_component
  rw [overlap.break_successor_eq]
  intro heq
  exact overlap.breakTarget_ne_target
    (heq.symm.trans overlap.breakSource_eq_target)

/-- The fixed target value at the shared edge. -/
def fixedColor : Color :=
  collar.targetCommonColoring overlap.commonEdge

/-- The value immediately before the final repair. -/
def repairOuterColor : Color :=
  collar.sourceCommonColoring overlap.repairSource overlap.commonEdge

/-- The value immediately after the earlier break. -/
def breakOuterColor : Color :=
  collar.sourceCommonColoring overlap.breakTarget overlap.commonEdge

theorem fixedColor_ne_zero : overlap.fixedColor ≠ 0 := by
  rw [fixedColor, ← overlap.start_eq_target,
    collar.sourceCommonColoring_apply_commonEdgeInSource]
  exact start.isTait _

theorem repairOuterColor_ne_zero : overlap.repairOuterColor ≠ 0 := by
  rw [repairOuterColor,
    collar.sourceCommonColoring_apply_commonEdgeInSource]
  exact overlap.repairSource.isTait _

theorem breakOuterColor_ne_zero : overlap.breakOuterColor ≠ 0 := by
  rw [breakOuterColor,
    collar.sourceCommonColoring_apply_commonEdgeInSource]
  exact overlap.breakTarget.isTait _

theorem repairOuterColor_ne_fixedColor :
    overlap.repairOuterColor ≠ overlap.fixedColor := by
  exact overlap.repairSource_ne_target

theorem breakOuterColor_ne_fixedColor :
    overlap.breakOuterColor ≠ overlap.fixedColor := by
  exact overlap.breakTarget_ne_target

/-- The repair component's selected pair is exactly the repair outer color
and the fixed target color, with the orientation determined by the source. -/
theorem repairPair_orientation :
    (overlap.repairOuterColor =
          crossFaceZeroColor
            overlap.repairStep.firstHit.transfer.coordinate ∧
        overlap.fixedColor =
          overlap.repairStep.reentry.realization.companion) ∨
      (overlap.repairOuterColor =
          overlap.repairStep.reentry.realization.companion ∧
        overlap.fixedColor =
          crossFaceZeroColor
            overlap.repairStep.firstHit.transfer.coordinate) := by
  simpa only [repairOuterColor, fixedColor,
      overlap.repair_successor_eq, overlap.start_eq_target] using
    overlap.repairStep.commonEdge_color_orientation overlap.commonEdge
      overlap.repairEdge_mem_component

/-- The break component's selected pair is exactly the fixed target color
and the break outer color, with the orientation determined by the source. -/
theorem breakPair_orientation :
    (overlap.fixedColor =
          crossFaceZeroColor
            overlap.breakStep.firstHit.transfer.coordinate ∧
        overlap.breakOuterColor =
          overlap.breakStep.reentry.realization.companion) ∨
      (overlap.fixedColor =
          overlap.breakStep.reentry.realization.companion ∧
        overlap.breakOuterColor =
          crossFaceZeroColor
            overlap.breakStep.firstHit.transfer.coordinate) := by
  simpa only [fixedColor, breakOuterColor,
      overlap.break_successor_eq, overlap.breakSource_eq_target] using
    overlap.breakStep.commonEdge_color_orientation overlap.commonEdge
      overlap.breakEdge_mem_component

/-- At the shared edge, the two component actions either use the same outer
color or the break action uses the unique third nonzero color. -/
theorem repairOuterColor_eq_breakOuterColor_or_threeColorTurn :
    overlap.repairOuterColor = overlap.breakOuterColor ∨
      overlap.breakOuterColor =
        overlap.fixedColor + overlap.repairOuterColor := by
  by_cases heq : overlap.repairOuterColor = overlap.breakOuterColor
  · exact Or.inl heq
  · exact Or.inr (color_eq_add_of_three_distinct_nonzero
      overlap.breakOuterColor_ne_zero overlap.fixedColor_ne_zero
      overlap.repairOuterColor_ne_zero
      overlap.breakOuterColor_ne_fixedColor (Ne.symm heq)
      overlap.repairOuterColor_ne_fixedColor.symm)

end CompanionRepairBreakOverlap

/-- A closed companion circuit yields an ordered repair--break overlap with
both actual Kempe components and the entire intervening suffix retained. -/
theorem nonempty_companionRepairBreakOverlap_of_closedCircuit
    {start : sourceNormal.KempeOrbitAdjacentEscape}
    (closed : Relation.TransGen
      (CompanionAdjacentEscapeTransition collar) start start) :
    Nonempty (CompanionRepairBreakOverlap collar start) := by
  rcases (Relation.transGen_iff
      (CompanionAdjacentEscapeTransition collar) start start).1 closed with
    hself | ⟨repairSource, hprefix, hrepair⟩
  · exact False.elim (hself.ne rfl)
  · rcases hrepair.exists_repairedCommonEdge with
      ⟨edge, hrepairSource, hstart⟩
    let predicate := fun escape : sourceNormal.KempeOrbitAdjacentEscape =>
      collar.sourceCommonColoring escape edge =
        collar.targetCommonColoring edge
    rcases reflTransGen_exists_predicate_break_with_suffix predicate
        hprefix.to_reflTransGen hstart hrepairSource with
      ⟨breakSource, breakTarget, hbreakReach, hbreak,
        hbreakSuffix, hbefore, hafter⟩
    rcases hrepair with ⟨repairStep, hrepairSuccessor⟩
    rcases hbreak with ⟨breakStep, hbreakSuccessor⟩
    exact ⟨{
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
      reach_repair_after_break := hbreakSuffix
      repairSource_ne_target := hrepairSource
      start_eq_target := hstart
      breakSource_eq_target := hbefore
      breakTarget_ne_target := hafter }⟩

/-- Every closed companion circuit has an actual shared-edge component
overlap which is either a same-outer-color return or a three-color turn. -/
theorem closedCircuit_exists_sameOuterRepairBreak_or_threeColorTurn
    {start : sourceNormal.KempeOrbitAdjacentEscape}
    (closed : Relation.TransGen
      (CompanionAdjacentEscapeTransition collar) start start) :
    (∃ overlap : CompanionRepairBreakOverlap collar start,
        overlap.repairOuterColor = overlap.breakOuterColor) ∨
      ∃ overlap : CompanionRepairBreakOverlap collar start,
        overlap.breakOuterColor =
          overlap.fixedColor + overlap.repairOuterColor := by
  rcases nonempty_companionRepairBreakOverlap_of_closedCircuit closed with
    ⟨overlap⟩
  rcases overlap.repairOuterColor_eq_breakOuterColor_or_threeColorTurn with
    hsame | hturn
  · exact Or.inl ⟨overlap, hsame⟩
  · exact Or.inr ⟨overlap, hturn⟩

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
