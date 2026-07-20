import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeResolution

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

namespace GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
namespace RotationOrderedCyclicKempeFusionChainNormalForm

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}
  {normal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}

namespace KempeOrbitAdjacentEscape

/-- A canonical adjacent escape is determined by its actual edge coloring. -/
@[ext]
theorem ext
    {first second : normal.KempeOrbitAdjacentEscape}
    (coloring_eq : first.coloring = second.coloring) : first = second := by
  cases first
  cases second
  cases coloring_eq
  rfl

end KempeOrbitAdjacentEscape

/-- The canonical adjacent escapes of a fixed normal form constitute a finite
state space. -/
noncomputable instance kempeOrbitAdjacentEscapeFinite :
    Finite normal.KempeOrbitAdjacentEscape :=
  Finite.of_injective KempeOrbitAdjacentEscape.coloring
    (fun _ _ => KempeOrbitAdjacentEscape.ext)

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

/-- The exact one-component Kempe transition between canonical adjacent
escapes on the fixed source deletion. -/
def AdjacentEscapeKempeStep
    (first second : sourceNormal.KempeOrbitAdjacentEscape) : Prop :=
  (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).EdgeKempeStep
    first.coloring second.coloring

/-- A nonrecursive certified outcome at a canonical adjacent escape. -/
inductive CertifiedAdjacentEscapeTerminal
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (escape : sourceNormal.KempeOrbitAdjacentEscape) : Prop
  | resolvedFusion
      (step : sourceNormal.ResolvedSameBaseKempeStep escape)
  | chargedReentry
      (resolution : ResolvedChargedKempeReentry collar escape)
  | supportedPrimalCycle
      (cycleRoot : collar.commonCoreVertex)
      (primalCycle : collar.commonCore.Walk cycleRoot cycleRoot)
      (isCycle : primalCycle.IsCycle)
      (length : 5 ≤ primalCycle.length)
  | returnChirality
      (boundary : ScalarCompanionTurnState.ImmediateReturnBoundary
        (collar := collar) (sourceEscape := escape))
      (lens : boundary.ExactReverseArrivalLens)
      (uniqueChirality : ∃! chirality : Bool,
        boundary.reverseTargetState lens.firstTurn =
          ScalarCompanionTurnState.ImmediateReturnBoundary.ExactReverseArrivalLens.chiralTargetState
            (boundary := boundary) chirality)

/-- Each canonical adjacent escape is terminal in the certified sense or has
an exact one-component transition to another canonical adjacent escape. -/
theorem certifiedAdjacentEscapeTerminal_or_exists_kempeStep
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (escape : sourceNormal.KempeOrbitAdjacentEscape) :
    CertifiedAdjacentEscapeTerminal collar escape ∨
      ∃ successor, collar.AdjacentEscapeKempeStep escape successor := by
  rcases collar.nonempty_adjacentEscapeResolution escape with ⟨resolution⟩
  cases resolution with
  | resolvedFusion step =>
      exact Or.inl (.resolvedFusion step)
  | adjacentReentry step =>
      exact Or.inr ⟨step.successor, step.oneStep⟩
  | chargedReentry resolution =>
      exact Or.inl (.chargedReentry resolution)
  | supportedPrimalCycle cycleRoot primalCycle isCycle length =>
      exact Or.inl (.supportedPrimalCycle cycleRoot primalCycle isCycle length)
  | returnChirality boundary lens uniqueChirality =>
      exact Or.inl (.returnChirality boundary lens uniqueChirality)

/-- Finite iteration of the sole adjacent residue reaches a certified
nonrecursive outcome or a reachable nonempty closed Kempe circuit. -/
theorem exists_reachable_certifiedAdjacentEscapeTerminal_or_kempeCycle
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) :
    (∃ finish,
        Relation.ReflTransGen collar.AdjacentEscapeKempeStep start finish ∧
          CertifiedAdjacentEscapeTerminal collar finish) ∨
      ∃ cycleState,
        Relation.ReflTransGen collar.AdjacentEscapeKempeStep start cycleState ∧
          Relation.TransGen collar.AdjacentEscapeKempeStep
            cycleState cycleState := by
  exact finite_reflTransGen_terminal_or_transGen_cycle
    collar.AdjacentEscapeKempeStep
    (CertifiedAdjacentEscapeTerminal collar)
    collar.certifiedAdjacentEscapeTerminal_or_exists_kempeStep start

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
