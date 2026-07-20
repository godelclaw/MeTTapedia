import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionResolvedKempeReentry

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

/-- Swapping two distinct colors on a Kempe component changes the coloring. -/
theorem kempeComponentSwap_ne_of_distinct
    {Vertex Color : Type*} {H : SimpleGraph Vertex} [DecidableEq Color]
    (C : H.Coloring Color) {first second : Color} (hne : first ≠ second)
    (component : (C.bicoloredSubgraph first second).ConnectedComponent) :
    C.swapOnKempeComponent first second component ≠ C := by
  intro heq
  rcases component.nonempty_supp with ⟨vertex, hvertex⟩
  have hcomponent : vertex.1 ∈
      C.kempeComponentSet first second component :=
    ⟨vertex.2, hvertex⟩
  have hvalue := congrArg (fun coloring : H.Coloring Color =>
    coloring vertex.1) heq
  rw [C.swapOnKempeComponent_apply_of_mem hcomponent] at hvalue
  rcases vertex.2 with hcolor | hcolor
  · rw [hcolor, Equiv.swap_apply_left] at hvalue
    exact hne hvalue.symm
  · rw [hcolor, Equiv.swap_apply_right] at hvalue
    exact hne hvalue

namespace GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
namespace RotationOrderedCyclicKempeFusionChainNormalForm

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- A same-base adjacent step whose retained component realization proves
that the successor coloring is genuinely different. -/
structure ProperAdjacentSameBaseKempeStep
    (normal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData)
    (escape : normal.KempeOrbitAdjacentEscape)
    extends normal.AdjacentSameBaseKempeStep escape where
  coloring_ne : successor.coloring ≠ escape.coloring

end RotationOrderedCyclicKempeFusionChainNormalForm
end GoertzelV24RecoveredAdjacentPairFusionChainNormalForm

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

namespace FirstHitSingletonCompanionTransferPath.TransverseCompanionChange

variable {firstHit : FirstHitSingletonCompanionTransferPath
    (collar := collar) (sourceEscape := sourceEscape)}
  (change : firstHit.TransverseCompanionChange)

/-- A transverse first-hit companion change is already a signed scalar turn. -/
def toScalarCompanionTurn :
    collar.ScalarCompanionTurn sourceEscape firstHit.transfer.coordinate := {
  first := change.resolved.first.1
  second := change.resolved.second.1
  third := change.thirdEdge
  firstSecond := change.resolved.firstSecond
  firstThird := change.firstThird
  secondThird := change.secondThird
  firstSupport := by
    simpa only [commonDiscrepancy_apply] using
      firstHit.transfer.support change.resolved.first.1
        change.resolved.first.2
  secondSupport := by
    simpa only [commonDiscrepancy_apply] using
      firstHit.transfer.support change.resolved.second.1
        change.resolved.second.2
  companion_ne := by
    simpa only [IntrinsicShortTargetEscapeCollar.discrepancyColorState,
      SingletonCompanionTransferPath.supportEdgeState,
      SingletonCompanionTransferPath.stateOfEdge] using
        change.resolved.companion_ne
  thirdDiscrepancy := by
    simpa only [commonDiscrepancy_apply] using change.discrepancy }

end FirstHitSingletonCompanionTransferPath.TransverseCompanionChange

/-- Exhaustive one-step outcome for a canonical adjacent escape.  The only
recursive residue is another adjacent escape on the same deleted-pair graph. -/
inductive AdjacentEscapeResolution
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) : Type (u + 1)
  | resolvedFusion
      (step : sourceNormal.ResolvedSameBaseKempeStep sourceEscape)
  | adjacentReentry
      (step : sourceNormal.AdjacentSameBaseKempeStep sourceEscape)
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

/-- Every adjacent escape has an exact local continuation: resolved fusion,
same-base adjacent reentry, charged reentry, a long supported cycle, or a
binary reverse-return chirality certificate. -/
theorem nonempty_adjacentEscapeResolution
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    Nonempty (AdjacentEscapeResolution collar sourceEscape) := by
  rcases collar.nonempty_firstHitSingletonCompanionTransferPath sourceEscape with
    ⟨firstHit⟩
  rcases firstHit.resolvedFusion_or_adjacentReentry_or_transverseChange with
    hresolved | hadjacent | htransverse
  · rcases hresolved with
      ⟨successorNormal, honeStep, hprofile, houtcome⟩
    exact ⟨.resolvedFusion {
      successorNormal := successorNormal
      oneStep := honeStep
      profileColoring_eq_recoloring := hprofile
      outcome := houtcome }⟩
  · rcases hadjacent with ⟨successor, honeStep⟩
    exact ⟨.adjacentReentry {
      successor := successor
      oneStep := honeStep }⟩
  · rcases htransverse with ⟨change⟩
    rcases change.toScalarCompanionTurn.hasResolvedKempeReentry_or_supportedPrimalCycle_or_uniqueReturnChirality with
      hcharged | hcycle | hreturn
    · rcases hcharged with ⟨resolution⟩
      exact ⟨.chargedReentry resolution⟩
    · rcases hcycle with ⟨cycleRoot, primalCycle, hisCycle, hlength⟩
      exact ⟨.supportedPrimalCycle cycleRoot primalCycle hisCycle hlength⟩
    · rcases hreturn with ⟨boundary, lens, hunique⟩
      exact ⟨.returnChirality boundary lens hunique⟩

/-- Exhaustive one-step outcome with a provably nonidentity recursive branch. -/
inductive ProperAdjacentEscapeResolution
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) : Type (u + 1)
  | resolvedFusion
      (step : sourceNormal.ResolvedSameBaseKempeStep sourceEscape)
  | adjacentReentry
      (step : sourceNormal.ProperAdjacentSameBaseKempeStep sourceEscape)
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
same-base transition changes the actual coloring. -/
theorem nonempty_properAdjacentEscapeResolution
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    Nonempty (ProperAdjacentEscapeResolution collar sourceEscape) := by
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
    have hrealizationNe : reentry.realization.coloring ≠
        sourceEscape.coloring := by
      exact kempeComponentSwap_ne_of_distinct
        sourceEscape.coloring
        (Ne.symm reentry.realization.companion_ne_distinguished)
        reentry.realization.component
    exact ⟨.adjacentReentry {
      successor := reentry.successor
      oneStep := by
        simpa only [reentry.coloring_eq] using reentry.realization.oneStep
      coloring_ne := fun heq =>
        hrealizationNe (reentry.coloring_eq.symm.trans heq) }⟩
  · rcases htransverse with ⟨change⟩
    rcases change.toScalarCompanionTurn.hasResolvedKempeReentry_or_supportedPrimalCycle_or_uniqueReturnChirality with
      hcharged | hcycle | hreturn
    · rcases hcharged with ⟨resolution⟩
      exact ⟨.chargedReentry resolution⟩
    · rcases hcycle with ⟨cycleRoot, primalCycle, hisCycle, hlength⟩
      exact ⟨.supportedPrimalCycle cycleRoot primalCycle hisCycle hlength⟩
    · rcases hreturn with ⟨boundary, lens, hunique⟩
      exact ⟨.returnChirality boundary lens hunique⟩

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
