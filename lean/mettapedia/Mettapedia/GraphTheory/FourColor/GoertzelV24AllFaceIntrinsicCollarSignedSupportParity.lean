import Mathlib.GroupTheory.Perm.Sign
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarSignedSupportMonodromy

/-! Odd signed monodromy of an intrinsic singleton collar. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

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

namespace ScalarSupportCrossingState

variable (state : ScalarSupportCrossingState collar sourceEscape)

/-- The two physical crossings of an intrinsic singleton collar have
opposite local chiralities. -/
theorem targetRootedCrossingChirality_ne_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile)
    {first second : Fin state.targetRootedSupportOrder.length}
    (hne : first ≠ second) :
    state.targetRootedCrossingChirality first ≠
      state.targetRootedCrossingChirality second := by
  intro hchirality
  let side := fun vertex => vertex ∈ profile.component.supp
  have hsupportOpposite :
      side (state.supportDartAt first).fst ↔
        ¬ side (state.supportDartAt second).fst := by
    exact state.supportDartAt_fst_side_ne_of_singletonPrimalCutProfile
      profile hne
  have hremoteCoherent :
      side (state.remoteDartAt first).fst ↔
        side (state.remoteDartAt second).fst := by
    simpa [side, remoteDartAt] using
      cycle.leftFaceDartAt_side_coherent_all_of_boundary_eq
        side profile.component_boundary_eq
        (state.remoteStepAt first) (state.remoteStepAt second)
  cases hfirst : state.targetRootedCrossingChirality first with
  | false =>
      have hsecond : state.targetRootedCrossingChirality second = false := by
        rw [← hchirality]
        exact hfirst
      have hfirstReverse : state.remoteDartAt first =
          (state.supportDartAt first).symm :=
        (state.targetRootedCrossingChirality_eq_false_iff first).1 hfirst
      have hsecondReverse : state.remoteDartAt second =
          (state.supportDartAt second).symm :=
        (state.targetRootedCrossingChirality_eq_false_iff second).1 hsecond
      have hsupportSndCoherent :
          side (state.supportDartAt first).snd ↔
            side (state.supportDartAt second).snd := by
        rw [hfirstReverse, hsecondReverse] at hremoteCoherent
        exact hremoteCoherent
      have hfirstCross :=
        state.supportDartAt_crosses_singletonSide profile first
      have hsecondCross :=
        state.supportDartAt_crosses_singletonSide profile second
      have hsupportCoherent :
          side (state.supportDartAt first).fst ↔
            side (state.supportDartAt second).fst := by
        tauto
      tauto
  | true =>
      have hsecond : state.targetRootedCrossingChirality second = true := by
        rw [← hchirality]
        exact hfirst
      have hfirstSame : state.remoteDartAt first =
          state.supportDartAt first :=
        (state.targetRootedCrossingChirality_eq_true_iff first).1 hfirst
      have hsecondSame : state.remoteDartAt second =
          state.supportDartAt second :=
        (state.targetRootedCrossingChirality_eq_true_iff second).1 hsecond
      have hsupportCoherent :
          side (state.supportDartAt first).fst ↔
            side (state.supportDartAt second).fst := by
        rw [← hfirstSame, ← hsecondSame]
        exact hremoteCoherent
      tauto

/-- Exactly one of the two singleton-collar crossing positions reverses
the support orientation. -/
theorem exists_unique_targetRootedCrossingChirality_eq_false_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile) :
    ∃! position : Fin state.targetRootedSupportOrder.length,
      state.targetRootedCrossingChirality position = false := by
  let first := state.targetRootedSupportEntryPosition
  let second := finRotate state.targetRootedSupportOrder.length first
  have htwo : 2 ≤ state.targetRootedSupportOrder.length :=
    state.two_le_targetRootedSupportOrder_length
  have hsecondNeFirst : second ≠ first := by
    rw [← Equiv.Perm.mem_support,
      support_finRotate_of_le htwo]
    exact Finset.mem_univ _
  have hfirstNeSecond : first ≠ second := hsecondNeFirst.symm
  have hchiralitiesNe :=
    state.targetRootedCrossingChirality_ne_of_singletonPrimalCutProfile
      profile hfirstNeSecond
  cases hfirst : state.targetRootedCrossingChirality first with
  | false =>
      refine ⟨first, hfirst, ?_⟩
      intro position hposition
      by_contra hne
      exact
        (state.targetRootedCrossingChirality_ne_of_singletonPrimalCutProfile
          profile hne) (hposition.trans hfirst.symm)
  | true =>
      have hsecond : state.targetRootedCrossingChirality second = false := by
        cases hvalue : state.targetRootedCrossingChirality second with
        | false => rfl
        | true =>
            exact False.elim
              (hchiralitiesNe (hfirst.trans hvalue.symm))
      refine ⟨second, hsecond, ?_⟩
      intro position hposition
      by_contra hne
      exact
        (state.targetRootedCrossingChirality_ne_of_singletonPrimalCutProfile
          profile hne) (hposition.trans hsecond.symm)

/-- Singleton signed monodromy is literally the transposition of the two
endpoint orientations at its unique reversed crossing. -/
theorem exists_targetRootedSignedMonodromy_eq_swap_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile) :
    ∃ negative : Fin state.targetRootedSupportOrder.length,
      state.targetRootedCrossingChirality negative = false ∧
        state.targetRootedSignedMonodromy =
          Equiv.swap (negative, false) (negative, true) := by
  rcases
      state.exists_unique_targetRootedCrossingChirality_eq_false_of_singletonPrimalCutProfile
        profile with ⟨negative, hnegative, hunique⟩
  refine ⟨negative, hnegative, ?_⟩
  apply Equiv.ext
  rintro ⟨position, endpoint⟩
  by_cases hposition : position = negative
  · subst position
    cases endpoint <;>
      simp [state.targetRootedSignedMonodromy_apply_of_singletonPrimalCutProfile
        profile, hnegative]
  · have hpositive :
        state.targetRootedCrossingChirality position = true := by
      cases hvalue : state.targetRootedCrossingChirality position with
      | false => exact False.elim (hposition (hunique position hvalue))
      | true => rfl
    have hneFalse : (position, endpoint) ≠ (negative, false) := by
      intro heq
      exact hposition (congrArg Prod.fst heq)
    have hneTrue : (position, endpoint) ≠ (negative, true) := by
      intro heq
      exact hposition (congrArg Prod.fst heq)
    rw [state.targetRootedSignedMonodromy_apply_of_singletonPrimalCutProfile
      profile, hpositive, fusionEndpointTransport_true,
      Equiv.swap_apply_of_ne_of_ne hneFalse hneTrue]

/-- The exact singleton-collar transposition is odd. -/
theorem targetRootedSignedMonodromy_sign_eq_neg_one_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile) :
    Equiv.Perm.sign state.targetRootedSignedMonodromy = -1 := by
  rcases
      state.exists_targetRootedSignedMonodromy_eq_swap_of_singletonPrimalCutProfile
        profile with ⟨negative, _hnegative, hmonodromy⟩
  rw [hmonodromy]
  exact Equiv.Perm.sign_swap (by simp)

end ScalarSupportCrossingState
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

namespace RotationOrderedFusionEscapeColorState

/-- An actual stateful reentry refined by intrinsic singleton geometry and
the resulting odd signed-support transport. -/
def IntrinsicOddSignedReentry
    (source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)) : Prop :=
  AdmissibleReentry source target ∧
    ∃ sourceNormal :
        RotationOrderedCyclicKempeFusionChainNormalForm graphData minimal
          source.1.1,
      ∃ sourceEscape : sourceNormal.KempeOrbitAdjacentEscape,
        source.1.2 = sourceEscape.coloring ∧
          ∃ targetEdge : G.edgeSet,
            centralEdge
                (RecoveredRotationOrderedData graphData minimal source.1.1) ≠
              targetEdge ∧
              centralEdge
                  (RecoveredRotationOrderedData graphData minimal target.1.1) =
                targetEdge ∧
                ∃ circuit : CrossCentralExactFaceCertifiedRebaseCircuit
                    graphData minimal source.1.1,
                  circuit.IsLengthMinimal ∧
                    ∃ cycle :
                        CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
                          circuit,
                      cycle.IntrinsicShortFusionTarget targetEdge ∧
                        ∃ collar :
                            cycle.IntrinsicShortTargetEscapeCollar targetEdge,
                          target.1 = ⟨collar.targetBase,
                            collar.targetEscape.coloring⟩ ∧
                            ∃ state :
                                collar.ScalarSupportCrossingState
                                  sourceEscape,
                              Equiv.Perm.sign
                                  state.targetRootedSignedMonodromy = -1

/-- An actual stateful reentry refined by its literal recovery transfer. -/
def RecoveryGeometricReentry
    (source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)) : Prop :=
  AdmissibleReentry source target ∧
    ∃ targetEdge : G.edgeSet,
      centralEdge
          (RecoveredRotationOrderedData graphData minimal source.1.1) ≠
        targetEdge ∧
        centralEdge
            (RecoveredRotationOrderedData graphData minimal target.1.1) =
          targetEdge ∧
          ∃ circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
              minimal source.1.1,
            circuit.IsLengthMinimal ∧
              ∃ rotated : CrossCentralExactFaceCertifiedRebaseCircuit graphData
                  minimal source.1.1,
                rotated.arcLength = circuit.arcLength ∧
                  ∃ transfer : ClosureRecoveryFaceTransfer rotated,
                    targetEdge = transfer.recovery.edge

/-- Every genuine all-face reentry is either an intrinsic odd signed step
or retains the exact recovery geometry that prevents that conclusion. -/
theorem AdmissibleReentry.intrinsicOddSigned_or_recoveryGeometric
    {source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)}
    (step : AdmissibleReentry source target) :
    IntrinsicOddSignedReentry source target ∨
      RecoveryGeometricReentry source target := by
  rcases step with
    ⟨sourceNormal, _sourceLaunch, sourceEscape, hsourceColor, targetEdge,
      htargetNe, htargetCentral, geometry, _targetNormal, _targetOutcome,
      _targetEscape, _htargetColor⟩
  rcases geometry with
    ⟨circuit, hminimal, cycle, hintrinsic, collar, htargetState⟩ |
      ⟨circuit, hminimal, rotated, hlength, transfer, htargetEdge⟩
  · let profile : cycle.SingletonPrimalCutProfile :=
      Classical.choice collar.singletonProfile
    let state : collar.ScalarSupportCrossingState sourceEscape :=
      Classical.choice (collar.exists_scalarSupportCrossingState sourceEscape)
    exact Or.inl ⟨by
      exact ⟨sourceNormal, by assumption, sourceEscape, hsourceColor,
        targetEdge, htargetNe, htargetCentral,
        Or.inl ⟨circuit, hminimal, cycle, hintrinsic, collar,
          htargetState⟩,
        ⟨_targetNormal, _targetOutcome, _targetEscape,
          _htargetColor⟩⟩,
      sourceNormal, sourceEscape, hsourceColor, targetEdge, htargetNe,
      htargetCentral, circuit, hminimal, cycle, hintrinsic, collar,
      htargetState, state,
      state.targetRootedSignedMonodromy_sign_eq_neg_one_of_singletonPrimalCutProfile
        profile⟩
  · exact Or.inr ⟨by
      exact ⟨sourceNormal, by assumption, sourceEscape, hsourceColor,
        targetEdge, htargetNe, htargetCentral,
        Or.inr ⟨circuit, hminimal, rotated, hlength, transfer,
          htargetEdge⟩,
        ⟨_targetNormal, _targetOutcome, _targetEscape,
          _htargetColor⟩⟩,
      targetEdge, htargetNe, htargetCentral, circuit, hminimal, rotated,
      hlength, transfer, htargetEdge⟩

/-- A nonempty stateful path either consists entirely of intrinsic odd
signed steps, or it exposes an exact recovery step together with the
original admissible prefix and suffix around it. -/
theorem transGen_intrinsicOddSigned_or_contains_recoveryGeometric
    {source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)}
    (path : Relation.TransGen
      (AdmissibleReentry (graphData := graphData) (minimal := minimal))
      source target) :
    Relation.TransGen
        (IntrinsicOddSignedReentry (graphData := graphData)
          (minimal := minimal)) source target ∨
      ∃ recoverySource recoveryTarget :
          AdmissibleState (graphData := graphData) (minimal := minimal),
        Relation.ReflTransGen
            (AdmissibleReentry (graphData := graphData) (minimal := minimal))
            source recoverySource ∧
          RecoveryGeometricReentry recoverySource recoveryTarget ∧
            Relation.ReflTransGen
              (AdmissibleReentry (graphData := graphData)
                (minimal := minimal)) recoveryTarget target := by
  induction path with
  | single step =>
      rcases step.intrinsicOddSigned_or_recoveryGeometric with
        hintrinsic | hrecovery
      · exact Or.inl (.single hintrinsic)
      · exact Or.inr ⟨_, _, .refl, hrecovery, .refl⟩
  | tail _ step ih =>
      rcases ih with
        hallIntrinsic |
          ⟨recoverySource, recoveryTarget, hprefix, hrecovery, hsuffix⟩
      · rcases step.intrinsicOddSigned_or_recoveryGeometric with
          hintrinsic | hrecovery
        · exact Or.inl (.tail hallIntrinsic hintrinsic)
        · exact Or.inr ⟨_, _,
            (hallIntrinsic.mono (fun _ _ intrinsic => intrinsic.1)
              ).to_reflTransGen,
            hrecovery, .refl⟩
      · exact Or.inr ⟨recoverySource, recoveryTarget, hprefix, hrecovery,
          Relation.ReflTransGen.tail hsuffix step⟩

end RotationOrderedFusionEscapeColorState
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
