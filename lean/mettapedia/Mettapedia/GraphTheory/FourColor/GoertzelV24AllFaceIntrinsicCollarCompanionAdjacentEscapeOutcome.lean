import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentFusionTargetCollarColorContact

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

/-- Finite companion iteration reaches a certified fixed-collar exit, or
reaches a closed circuit carrying one of the five classified local outcomes. -/
theorem exists_reachable_certifiedAdjacentEscapeTerminal_or_classifiedCompanionCycle
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) :
    (∃ finish,
        Relation.ReflTransGen (CompanionAdjacentEscapeTransition collar)
            start finish ∧
          CertifiedAdjacentEscapeTerminal collar finish) ∨
      ∃ cycleState,
        Relation.ReflTransGen (CompanionAdjacentEscapeTransition collar)
            start cycleState ∧
          (Nonempty
              (CompanionCanonicalComponentDisjointClosure collar cycleState) ∨
            Nonempty
                (CompanionCrossPairFusionTargetTransport collar cycleState) ∨
              Nonempty
                  (CompanionCrossPairFusionTargetCollarTraversal collar cycleState) ∨
                Nonempty
                    (CompanionSameOuterTargetAvoidingEdgePivot collar cycleState) ∨
                  Nonempty (CompanionThreePairMonodromy collar cycleState)) := by
  rcases collar.exists_reachable_certifiedAdjacentEscapeTerminal_or_companionCycle
      start with terminal | ⟨cycleState, reachable, closed⟩
  · exact Or.inl terminal
  · exact Or.inr ⟨cycleState, reachable,
      closedCircuit_exists_localCancellation_or_fusionTargetTransport_or_fusionTargetCollarTraversal_or_edgePivot_or_threePairMonodromy
        closed⟩

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
