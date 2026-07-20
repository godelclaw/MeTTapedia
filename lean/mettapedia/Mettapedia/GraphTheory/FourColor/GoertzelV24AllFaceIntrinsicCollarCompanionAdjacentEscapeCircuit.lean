import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeRecurrence

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

/-- Along a finite transition chain, if a predicate holds initially and
fails finally, one transition witnesses its first possible break. -/
theorem reflTransGen_exists_predicate_break
    {State : Type*} {relation : State → State → Prop}
    {start finish : State} (predicate : State → Prop)
    (reachable : Relation.ReflTransGen relation start finish)
    (atStart : predicate start) (notAtFinish : ¬predicate finish) :
    ∃ before after,
      Relation.ReflTransGen relation start before ∧
        relation before after ∧ predicate before ∧ ¬predicate after := by
  induction reachable with
  | refl => exact False.elim (notAtFinish atStart)
  | @tail middle finish reachable step ih =>
      by_cases atMiddle : predicate middle
      · exact ⟨middle, finish, reachable, step, atMiddle, notAtFinish⟩
      · exact ih atMiddle

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

/-- A recursive adjacent transition retaining the first-hit path and the
actual source-deletion component realization that it launches. -/
structure CompanionAdjacentEscapeStep
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) where
  firstHit : FirstHitSingletonCompanionTransferPath
    (collar := collar) (sourceEscape := sourceEscape)
  reentry : firstHit.transfer.AdjacentSourceOrbitReentry

namespace CompanionAdjacentEscapeStep

variable (step : CompanionAdjacentEscapeStep collar sourceEscape)

/-- The canonical adjacent successor reached by the retained component
swap. -/
def successor : sourceNormal.KempeOrbitAdjacentEscape :=
  step.reentry.successor

/-- The retained realization is a literal one-component Kempe step. -/
theorem oneStep :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
        collar.sourceData.secondVertex).EdgeKempeStep
      sourceEscape.coloring step.successor.coloring := by
  simpa only [successor, step.reentry.coloring_eq] using
    step.reentry.realization.oneStep

/-- The retained component uses two distinct colors. -/
theorem distinguished_ne_companion :
    crossFaceZeroColor step.firstHit.transfer.coordinate ≠
      step.reentry.realization.companion :=
  Ne.symm step.reentry.realization.companion_ne_distinguished

/-- The recursive successor is genuinely different from its source. -/
theorem successor_coloring_ne :
    step.successor.coloring ≠ sourceEscape.coloring := by
  intro heq
  apply kempeComponentSwap_ne_of_distinct sourceEscape.coloring
    step.distinguished_ne_companion step.reentry.realization.component
  exact step.reentry.coloring_eq.symm.trans heq

/-- Every edge on the retained first-hit support disagrees with the fixed
target before the component swap. -/
theorem source_ne_target_on_support
    (edge : step.firstHit.transfer.SupportEdge) :
    collar.sourceCommonColoring sourceEscape edge.1 ≠
      collar.targetCommonColoring edge.1 := by
  intro heq
  have hsupport := step.firstHit.transfer.support edge.1 edge.2
  rw [heq, color_add_self] at hsupport
  cases step.firstHit.transfer.coordinate <;>
    simp [crossFaceCoordinate] at hsupport

/-- Every edge on the retained first-hit support agrees with the fixed
target after the component swap. -/
theorem successor_eq_target_on_support
    (edge : step.firstHit.transfer.SupportEdge) :
    collar.sourceCommonColoring step.successor edge.1 =
      collar.targetCommonColoring edge.1 := by
  rw [collar.sourceCommonColoring_apply_commonEdgeInSource,
    successor, step.reentry.coloring_eq]
  apply step.reentry.realization.agrees_on_support edge
  exact List.mem_attach _ edge

/-- A provenance-retaining step repairs at least one explicit common-core
edge from disagreement to agreement with the fixed target coloring. -/
theorem exists_repairedCommonEdge :
    ∃ edge : collar.commonCore.edgeSet,
      collar.sourceCommonColoring sourceEscape edge ≠
          collar.targetCommonColoring edge ∧
        collar.sourceCommonColoring step.successor edge =
          collar.targetCommonColoring edge := by
  let edge := step.firstHit.transfer.supportEdgeWord.head
    step.firstHit.transfer.supportEdgeWord_ne_nil
  exact ⟨edge.1, step.source_ne_target_on_support edge,
    step.successor_eq_target_on_support edge⟩

end CompanionAdjacentEscapeStep

/-- Exhaustive local outcome retaining full first-hit provenance in the
only recursive branch. -/
inductive CompanionAdjacentEscapeResolution
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) : Type (u + 1)
  | resolvedFusion
      (step : sourceNormal.ResolvedSameBaseKempeStep sourceEscape)
  | adjacentReentry
      (step : CompanionAdjacentEscapeStep collar sourceEscape)
  | chargedReentry
      (resolution : ResolvedChargedKempeReentry collar sourceEscape)
  | supportedPrimalCycle
      (cycleRoot : collar.commonCoreVertex)
      (primalCycle : collar.commonCore.Walk cycleRoot cycleRoot)
      (isCycle : primalCycle.IsCycle)
      (length : 5 ≤ primalCycle.length)
  | returnChirality
      (boundary : ScalarCompanionTurnState.ImmediateReturnBoundary
        (collar := collar) (sourceEscape := sourceEscape))
      (lens : boundary.ExactReverseArrivalLens)
      (uniqueChirality : ∃! chirality : Bool,
        boundary.reverseTargetState lens.firstTurn =
          ScalarCompanionTurnState.ImmediateReturnBoundary.ExactReverseArrivalLens.chiralTargetState
            (boundary := boundary) chirality)

/-- Every adjacent escape has a complete local resolution whose recursive
branch retains the first-hit path and component realization. -/
theorem nonempty_companionAdjacentEscapeResolution
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    Nonempty (CompanionAdjacentEscapeResolution collar sourceEscape) := by
  rcases collar.nonempty_firstHitSingletonCompanionTransferPath sourceEscape with
    ⟨firstHit⟩
  rcases firstHit.allEqualFusionConnector_or_adjacentReentry_or_transverseChange with
    hallEqual | hadjacent | htransverse
  · rcases hallEqual with ⟨connector⟩
    rcases connector.exists_oneStep_resolvedNormalForm_and_outcome with
      ⟨successorNormal, _hrecoloring, honeStep, hprofile, houtcome⟩
    exact ⟨.resolvedFusion {
      successorNormal := successorNormal
      oneStep := honeStep
      profileColoring_eq_recoloring := hprofile
      outcome := houtcome }⟩
  · rcases hadjacent with ⟨reentry⟩
    exact ⟨.adjacentReentry {
      firstHit := firstHit
      reentry := reentry }⟩
  · rcases htransverse with ⟨change⟩
    rcases change.toScalarCompanionTurn.hasResolvedKempeReentry_or_supportedPrimalCycle_or_uniqueReturnChirality with
      hcharged | hcycle | hreturn
    · rcases hcharged with ⟨resolution⟩
      exact ⟨.chargedReentry resolution⟩
    · rcases hcycle with ⟨cycleRoot, primalCycle, hisCycle, hlength⟩
      exact ⟨.supportedPrimalCycle cycleRoot primalCycle hisCycle hlength⟩
    · rcases hreturn with ⟨boundary, lens, hunique⟩
      exact ⟨.returnChirality boundary lens hunique⟩

/-- The provenance-retaining recursive transition relation. -/
def CompanionAdjacentEscapeTransition
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (first second : sourceNormal.KempeOrbitAdjacentEscape) : Prop :=
  ∃ step : CompanionAdjacentEscapeStep collar first,
    step.successor = second

namespace CompanionAdjacentEscapeTransition

/-- A provenance-retaining transition projects to its exact Kempe step. -/
theorem oneStep
    {first second : sourceNormal.KempeOrbitAdjacentEscape}
    (transition : CompanionAdjacentEscapeTransition collar first second) :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
        collar.sourceData.secondVertex).EdgeKempeStep
      first.coloring second.coloring := by
  rcases transition with ⟨step, rfl⟩
  exact step.oneStep

/-- A provenance-retaining transition cannot be a self-loop. -/
theorem ne
    {first second : sourceNormal.KempeOrbitAdjacentEscape}
    (transition : CompanionAdjacentEscapeTransition collar first second) :
    first ≠ second := by
  intro heq
  subst second
  rcases transition with ⟨step, hsuccessor⟩
  exact step.successor_coloring_ne
    (congrArg (fun escape => escape.coloring) hsuccessor)

/-- Every transition retains an explicit common-core edge repaired against
the fixed target coloring. -/
theorem exists_repairedCommonEdge
    {first second : sourceNormal.KempeOrbitAdjacentEscape}
    (transition : CompanionAdjacentEscapeTransition collar first second) :
    ∃ edge : collar.commonCore.edgeSet,
      collar.sourceCommonColoring first edge ≠
          collar.targetCommonColoring edge ∧
        collar.sourceCommonColoring second edge =
          collar.targetCommonColoring edge := by
  rcases transition with ⟨step, rfl⟩
  exact step.exists_repairedCommonEdge

end CompanionAdjacentEscapeTransition

/-- Each state exits with a certified outcome or takes one
provenance-retaining companion transition. -/
theorem certifiedAdjacentEscapeTerminal_or_exists_companionTransition
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (escape : sourceNormal.KempeOrbitAdjacentEscape) :
    CertifiedAdjacentEscapeTerminal collar escape ∨
      ∃ successor,
        CompanionAdjacentEscapeTransition collar escape successor := by
  rcases collar.nonempty_companionAdjacentEscapeResolution escape with
    ⟨resolution⟩
  cases resolution with
  | resolvedFusion step =>
      exact Or.inl (CertifiedAdjacentEscapeTerminal.resolvedFusion step)
  | adjacentReentry step =>
      exact Or.inr ⟨step.successor, step, rfl⟩
  | chargedReentry resolution =>
      exact Or.inl
        (CertifiedAdjacentEscapeTerminal.chargedReentry resolution)
  | supportedPrimalCycle cycleRoot primalCycle isCycle length =>
      exact Or.inl (CertifiedAdjacentEscapeTerminal.supportedPrimalCycle
        cycleRoot primalCycle isCycle length)
  | returnChirality boundary lens uniqueChirality =>
      exact Or.inl (CertifiedAdjacentEscapeTerminal.returnChirality
        boundary lens uniqueChirality)

/-- Finite iteration with full path/component provenance reaches a certified
fixed-collar exit or a reachable nonempty closed companion circuit. -/
theorem exists_reachable_certifiedAdjacentEscapeTerminal_or_companionCycle
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) :
    (∃ finish,
        Relation.ReflTransGen (CompanionAdjacentEscapeTransition collar)
            start finish ∧
          CertifiedAdjacentEscapeTerminal collar finish) ∨
      ∃ cycleState,
        Relation.ReflTransGen (CompanionAdjacentEscapeTransition collar)
            start cycleState ∧
          Relation.TransGen (CompanionAdjacentEscapeTransition collar)
            cycleState cycleState := by
  exact finite_reflTransGen_terminal_or_transGen_cycle
    (CompanionAdjacentEscapeTransition collar)
    (CertifiedAdjacentEscapeTerminal collar)
    collar.certifiedAdjacentEscapeTerminal_or_exists_companionTransition start

/-- Every closed provenance-retaining companion circuit contains a repair
edge and, earlier around the same circuit, a transition which breaks that
agreement again. -/
theorem CompanionAdjacentEscapeTransition.closedCycle_exists_repair_and_break
    {start : sourceNormal.KempeOrbitAdjacentEscape}
    (closed : Relation.TransGen
      (CompanionAdjacentEscapeTransition collar) start start) :
    ∃ repairSource : sourceNormal.KempeOrbitAdjacentEscape,
      ∃ edge : collar.commonCore.edgeSet,
        ∃ breakSource breakTarget : sourceNormal.KempeOrbitAdjacentEscape,
          Relation.TransGen (CompanionAdjacentEscapeTransition collar)
              start repairSource ∧
            CompanionAdjacentEscapeTransition collar repairSource start ∧
            Relation.ReflTransGen (CompanionAdjacentEscapeTransition collar)
              start breakSource ∧
            CompanionAdjacentEscapeTransition collar breakSource breakTarget ∧
            collar.sourceCommonColoring repairSource edge ≠
              collar.targetCommonColoring edge ∧
            collar.sourceCommonColoring start edge =
              collar.targetCommonColoring edge ∧
            collar.sourceCommonColoring breakSource edge =
              collar.targetCommonColoring edge ∧
            collar.sourceCommonColoring breakTarget edge ≠
              collar.targetCommonColoring edge := by
  rcases (Relation.transGen_iff
      (CompanionAdjacentEscapeTransition collar) start start).1 closed with
    hself | ⟨repairSource, hprefix, hrepair⟩
  · exact False.elim (hself.ne rfl)
  · rcases hrepair.exists_repairedCommonEdge with
      ⟨edge, hrepairSource, hstart⟩
    let predicate := fun escape : sourceNormal.KempeOrbitAdjacentEscape =>
      collar.sourceCommonColoring escape edge =
        collar.targetCommonColoring edge
    rcases reflTransGen_exists_predicate_break predicate
        hprefix.to_reflTransGen hstart hrepairSource with
      ⟨breakSource, breakTarget, hbreakReach, hbreak, hbefore, hafter⟩
    exact ⟨repairSource, edge, breakSource, breakTarget,
      hprefix, hrepair, hbreakReach, hbreak,
      hrepairSource, hstart, hbefore, hafter⟩

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
