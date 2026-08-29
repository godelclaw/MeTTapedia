import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceEscapeStateColorGauge
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceEscapeStateMonodromy
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarSignedSupportParity

/-!
# Exact residue of the all-face escape-state machine

The finite all-face machine already reaches a structural target, a large
remote primal cut, or a nonempty closed reentry orbit.  This file refines the
last alternative without adding a supply hypothesis.  A closed orbit either
contains the literal recovery geometry, or every step carries the odd signed
monodromy of an intrinsic singleton collar.  In the all-intrinsic case the
ambient discrepancies telescope to zero, while every closed affine color
gauge word has identity linear holonomy and even sign.

This is a residue theorem, not a contradiction: a proof of wall exclusion
must still prevent cancellation of the local odd geometric charges, or reduce
the exact recovery branch.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24AllFaceEscapeStateCycleResidue

open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairInsertion.AdjacentPairData.RotationOrderedFusionEscapeColorState
open GoertzelV24AdjacentPairInsertion.AdjacentPairData.CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle.IntrinsicShortTargetEscapeCollar

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}

abbrev State :=
  RotationOrderedFusionEscapeColorState.AdmissibleState
    (graphData := graphData) (minimal := minimal)

abbrev Step :=
  RotationOrderedFusionEscapeColorState.AdmissibleReentry
    (graphData := graphData) (minimal := minimal)

/-- A closed all-face orbit with one explicitly located recovery step. -/
structure ClosedRecoveryResidue
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (state : State (graphData := graphData) (minimal := minimal)) where
  cycle : Relation.TransGen
    (Step (graphData := graphData) (minimal := minimal)) state state
  recoverySource : State (graphData := graphData) (minimal := minimal)
  recoveryTarget : State (graphData := graphData) (minimal := minimal)
  before : Relation.ReflTransGen
    (Step (graphData := graphData) (minimal := minimal)) state recoverySource
  recoveryStep :
    RotationOrderedFusionEscapeColorState.RecoveryGeometricReentry
      (graphData := graphData) (minimal := minimal)
      recoverySource recoveryTarget
  after : Relation.ReflTransGen
    (Step (graphData := graphData) (minimal := minimal)) recoveryTarget state

/-- A closed all-intrinsic orbit, retaining the three exact facts that any
global monodromy argument must reconcile: every local signed transport is
odd, the total ambient discrepancy is zero, and every closed affine color
gauge word is even. -/
structure ClosedIntrinsicResidue
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (state : State (graphData := graphData) (minimal := minimal)) where
  cycle : Relation.TransGen
    (Step (graphData := graphData) (minimal := minimal)) state state
  intrinsicCycle : Relation.TransGen
    (RotationOrderedFusionEscapeColorState.IntrinsicOddSignedReentry
      (graphData := graphData) (minimal := minimal)) state state
  discrepancyTotal : G.edgeSet → Color
  discrepancyPath :
    RotationOrderedFusionEscapeColorState.ReentryDiscrepancyChain
      state state discrepancyTotal
  discrepancy_zero : discrepancyTotal = 0
  affineWord :
    ∀ translation :
        RotationOrderedFusionEscapeColorState.ReentryTranslation
          (graphData := graphData) (minimal := minimal),
      ∃ word : List (Color × ColorNameSymmetry),
        RotationOrderedFusionEscapeColorState.ReentryColorGaugeWord
            translation state state word ∧
          colorAffineWordLinear word = 1 ∧
            Equiv.Perm.sign (colorAffineWordTransfer word) = 1

/-- Starting from any directed edge, the source-faithful all-face machine
reaches a structural target, reaches a large exact remote primal cut, or
enters one of two completely explicit closed residues. -/
theorem exists_reachable_structural_or_largeRemotePrimalCut_or_closedResidue
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (start : G.Dart) :
    ∃ initial : State (graphData := graphData) (minimal := minimal),
      initial.1.dart = start ∧
        ((∃ finish,
            Relation.ReflTransGen
                (Step (graphData := graphData) (minimal := minimal))
                initial finish ∧
              RotationOrderedFusionStructuralTargetAtDart graphData minimal
                finish.1.dart) ∨
          (∃ finish,
            Relation.ReflTransGen
                (Step (graphData := graphData) (minimal := minimal))
                initial finish ∧
              RotationOrderedFusionLargeRemotePrimalCutAtDart graphData
                minimal finish.1.dart) ∨
          ∃ cycleState,
            Relation.ReflTransGen
                (Step (graphData := graphData) (minimal := minimal))
                initial cycleState ∧
              (Nonempty (ClosedRecoveryResidue graphData minimal cycleState) ∨
                Nonempty (ClosedIntrinsicResidue graphData minimal cycleState))) := by
  rcases
      RotationOrderedFusionEscapeColorState.exists_escapeState_reachable_structural_or_largeRemotePrimalCut_or_reentryCycle
        graphData minimal start with
    ⟨initial, hinitial, hstructural | hlarge | hcycle⟩
  · exact ⟨initial, hinitial, Or.inl hstructural⟩
  · exact ⟨initial, hinitial, Or.inr (Or.inl hlarge)⟩
  · rcases hcycle with ⟨cycleState, hreach, cycle⟩
    refine ⟨initial, hinitial, Or.inr (Or.inr ⟨cycleState, hreach, ?_⟩)⟩
    rcases
        RotationOrderedFusionEscapeColorState.transGen_intrinsicOddSigned_or_contains_recoveryGeometric
          cycle with
      intrinsicCycle |
        ⟨recoverySource, recoveryTarget, before, recoveryStep, after⟩
    · rcases
          RotationOrderedFusionEscapeColorState.ReentryDiscrepancyChain.exists_eq_zero_of_transGen_cycle
            cycle with
        ⟨discrepancyTotal, discrepancyPath, discrepancyZero⟩
      refine Or.inr ⟨{
        cycle := cycle
        intrinsicCycle := intrinsicCycle
        discrepancyTotal := discrepancyTotal
        discrepancyPath := discrepancyPath
        discrepancy_zero := discrepancyZero
        affineWord := ?_ }⟩
      intro translation
      exact
        RotationOrderedFusionEscapeColorState.ReentryColorGaugeWord.exists_closed_word_of_reentry_cycle
          translation cycle
    · exact Or.inl ⟨{
        cycle := cycle
        recoverySource := recoverySource
        recoveryTarget := recoveryTarget
        before := before
        recoveryStep := recoveryStep
        after := after }⟩

end GoertzelV24AllFaceEscapeStateCycleResidue

end

end Mettapedia.GraphTheory.FourColor
