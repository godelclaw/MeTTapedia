import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAllEqualFusionReentry

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

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
namespace RotationOrderedCyclicKempeFusionChainNormalForm

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

attribute [local instance]
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.fusionFaceNetworkGraphEdgeSetDecidableEq
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.fusionFaceNetworkRetainedVertexFintype
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.fusionFaceNetworkRetainedVertexDecidableEq

/-- A component swap landing in an all-equal sector, fully resolved at its
actual successor coloring. -/
structure ResolvedSameBaseKempeStep
    (normal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData)
    (escape : normal.KempeOrbitAdjacentEscape) where
  successorNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData
  oneStep : (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
      (RecoveredRotationOrderedData graphData minimal baseData).secondVertex
    ).EdgeKempeStep escape.coloring successorNormal.recoloring
  profileColoring_eq_recoloring :
    successorNormal.profile.coloring = successorNormal.recoloring
  outcome : successorNormal.TerminalFusionOutcome ∨
    successorNormal.CertifiedRebasePumpingLaunch

/-- A component swap remaining in the canonical adjacent sector. -/
structure AdjacentSameBaseKempeStep
    (normal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData)
    (escape : normal.KempeOrbitAdjacentEscape) where
  successor : normal.KempeOrbitAdjacentEscape
  oneStep : (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
      (RecoveredRotationOrderedData graphData minimal baseData).secondVertex
    ).EdgeKempeStep escape.coloring successor.coloring

namespace SameBaseKempeReentry

variable {normal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {escape : normal.KempeOrbitAdjacentEscape}

/-- Exact continuation package for a same-base reentry. -/
theorem resolvedStep_or_adjacentStep
    (reentry : normal.SameBaseKempeReentry escape) :
    Nonempty (ResolvedSameBaseKempeStep normal escape) ∨
      Nonempty (AdjacentSameBaseKempeStep normal escape) := by
  rcases reentry.resolvedNormalForm_or_adjacentEscape with
    ⟨successorNormal, honeStep, hprofile, houtcome⟩ |
      ⟨successor, honeStep⟩
  · exact Or.inl ⟨{
      successorNormal := successorNormal
      oneStep := honeStep
      profileColoring_eq_recoloring := hprofile
      outcome := houtcome }⟩
  · exact Or.inr ⟨{
      successor := successor
      oneStep := honeStep }⟩

end SameBaseKempeReentry
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

/-- A charged terminal action together with its fully classified same-base
continuation on the source or target adjacent-pair deletion. -/
structure ResolvedChargedKempeReentry
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) where
  coordinate : Bool
  representative : IntrinsicCollarTerminalRepresentative
    collar.intrinsicCollarPortOverlapProfile
  action : ChargedTerminalKempeAction collar sourceEscape coordinate
    representative
  continuation :
    Nonempty (sourceNormal.ResolvedSameBaseKempeStep sourceEscape) ∨
      Nonempty (sourceNormal.AdjacentSameBaseKempeStep sourceEscape) ∨
      Nonempty (collar.targetNormal.ResolvedSameBaseKempeStep
        collar.targetEscape) ∨
      Nonempty (collar.targetNormal.AdjacentSameBaseKempeStep
        collar.targetEscape)

/-- Every charged Kempe reentry has a resolved source-or-target continuation. -/
theorem HasChargedKempeReentry.nonempty_resolved
    (reentry : collar.HasChargedKempeReentry sourceEscape) :
    Nonempty (ResolvedChargedKempeReentry collar sourceEscape) := by
  rcases reentry with
    ⟨coordinate, representative, action, hsource | htarget⟩
  · rcases hsource.resolvedStep_or_adjacentStep with
      hresolved | hadjacent
    · exact ⟨{
        coordinate := coordinate
        representative := representative
        action := action
        continuation := Or.inl hresolved }⟩
    · exact ⟨{
        coordinate := coordinate
        representative := representative
        action := action
        continuation := Or.inr (Or.inl hadjacent) }⟩
  · rcases htarget.resolvedStep_or_adjacentStep with
      hresolved | hadjacent
    · exact ⟨{
        coordinate := coordinate
        representative := representative
        action := action
        continuation := Or.inr (Or.inr (Or.inl hresolved)) }⟩
    · exact ⟨{
        coordinate := coordinate
        representative := representative
        action := action
        continuation := Or.inr (Or.inr (Or.inr hadjacent)) }⟩

namespace ScalarCompanionTurn

variable {coordinate : Bool}

/-- A signed scalar turn reaches a resolved charged continuation, a supported
primal cycle, or the exact binary return lens. -/
theorem hasResolvedKempeReentry_or_supportedPrimalCycle_or_uniqueReturnChirality
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    Nonempty (ResolvedChargedKempeReentry collar sourceEscape) ∨
      (∃ (cycleRoot : collar.commonCoreVertex)
          (primalCycle : collar.commonCore.Walk cycleRoot cycleRoot),
        primalCycle.IsCycle ∧ 5 ≤ primalCycle.length) ∨
      ∃ boundary : ScalarCompanionTurnState.ImmediateReturnBoundary
          (collar := collar) (sourceEscape := sourceEscape),
        ∃ lens : boundary.ExactReverseArrivalLens,
          ∃! chirality : Bool,
            boundary.reverseTargetState lens.firstTurn =
              ScalarCompanionTurnState.ImmediateReturnBoundary.ExactReverseArrivalLens.chiralTargetState
                (boundary := boundary) chirality := by
  rcases turn.hasChargedKempeReentry_or_supportedPrimalCycle_or_uniqueReturnChirality
      with hcharged | hcycle | hreturn
  · exact Or.inl hcharged.nonempty_resolved
  · exact Or.inr (Or.inl hcycle)
  · exact Or.inr (Or.inr hreturn)

end ScalarCompanionTurn

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
