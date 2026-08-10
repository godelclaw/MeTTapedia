import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationInvariant
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16SignedOrbitCoinvariants

/-!
# OUR bounded trace-functional certificate for an incoming commutator pair

This module constructs an explicit trace functional on the ordinary
derivative-free eight-field trace quotient.  Its two literal sources are kept
independent of representative-chart payloads.  The finite calculation is
factored through the 24 unsigned coordinate permutations and a
kernel-checked reflection-invariance lemma.

The result concerns the isolated ordinary trace quotient only.  The separate
comparison module identifies these literal sources with the incoming
covariant-commutator component of the physical relation operator.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16IncomingCommutatorTraceCertificate

open V14HypercubicFDCensus
open HypercubicRawFDCharacterCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16PhysicalTraceEvaluationMatrices
open HypercubicDimension16PhysicalTraceEvaluationInvariant
open HypercubicDimension16TraceEvaluation

/-- OUR literal realization of the trace immediately before the distinguished
field insertion. -/
def incomingBeforeTrace : Equiv.Perm (Fin 8) where
  toFun := fun field => Fin.ofNat 8
    (#[1, 2, 3, 4, 5, 6, 7, 0].getD field.1 0)
  invFun := fun field => Fin.ofNat 8
    (#[7, 0, 1, 2, 3, 4, 5, 6].getD field.1 0)
  left_inv := by intro field; fin_cases field <;> decide +kernel
  right_inv := by intro field; fin_cases field <;> decide +kernel

/-- OUR literal realization of the trace immediately after the distinguished
field insertion. -/
def incomingAfterTrace : Equiv.Perm (Fin 8) where
  toFun := fun field => Fin.ofNat 8
    (#[7, 2, 3, 4, 5, 6, 0, 1].getD field.1 0)
  invFun := fun field => Fin.ofNat 8
    (#[6, 7, 1, 2, 3, 4, 5, 0].getD field.1 0)
  left_inv := by intro field; fin_cases field <;> decide +kernel
  right_inv := by intro field; fin_cases field <;> decide +kernel

/-- OUR common derivative-free decoration of the two literal sources. -/
def incomingDecoration : LocalWordDecoration 8 0 :=
  ⟨fun field =>
      { plane := Fin.ofNat 6
          (#[5, 4, 0, 0, 0, 0, 0, 1].getD field.1 0)
        derivativeCount := 0
        derivativeAxis := Fin.elim0 }, by simp⟩

/-- OUR first literal source of the signed incoming pair. -/
def incomingBeforeSource : LabeledLocalWordSector 8 0 where
  trace := incomingBeforeTrace
  decoration := incomingDecoration

/-- OUR second literal source of the signed incoming pair. -/
def incomingAfterSource : LabeledLocalWordSector 8 0 where
  trace := incomingAfterTrace
  decoration := incomingDecoration

/-- OUR reflection block above one unsigned coordinate permutation. -/
def sourceReflectionBlock
    (source : LabeledLocalWordSector 8 0) (permutation : Fin 24) : ℚ :=
  ∑ reflectionMask : Fin 16,
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    source.tensorSign h *
      labeledPlaneTraceEvaluation (encodedEvaluationMatrixAt ⟨6, by decide⟩)
        (source.hypercubicAct h)

/-- OUR one-reflection representative of a permutation block. -/
def sourcePermutationContribution
    (source : LabeledLocalWordSector 8 0) (permutation : Fin 24) : ℚ :=
  let h := decodedHypercubicCharacterElement permutation 0
  source.tensorSign h *
    labeledPlaneTraceEvaluation (encodedEvaluationMatrixAt ⟨6, by decide⟩)
      (source.hypercubicAct h)

/-- OUR compact expected table for the first source. -/
def expectedBeforePermutationContribution : Fin 24 → ℚ
  | 0 | 2 | 7 | 13 => 1
  | _ => 0

/-- OUR compact expected table for the second source. -/
def expectedAfterPermutationContribution : Fin 24 → ℚ
  | 0 | 2 => -1
  | 7 | 13 => 1
  | _ => 0

/-- OUR action of a fixed unsigned permutation is independent of the
reflection mask on the first source. -/
theorem incomingBefore_action_reflection_invariant
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    incomingBeforeSource.hypercubicAct
        (decodedHypercubicCharacterElement permutation reflectionMask) =
      incomingBeforeSource.hypercubicAct
        (decodedHypercubicCharacterElement permutation 0) := by
  rfl

/- OUR kernel-checked cancellation of reflection signs in the first source. -/
set_option maxHeartbeats 2000000 in
theorem incomingBefore_tensorSign_reflection_invariant
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    incomingBeforeSource.tensorSign
        (decodedHypercubicCharacterElement permutation reflectionMask) =
      incomingBeforeSource.tensorSign
        (decodedHypercubicCharacterElement permutation 0) := by
  set_option maxRecDepth 100000 in
    fin_cases permutation <;> fin_cases reflectionMask <;> decide +kernel

/-- OUR factorization of each first-source reflection summand. -/
theorem incomingBefore_reflection_term
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    incomingBeforeSource.tensorSign h *
      labeledPlaneTraceEvaluation (encodedEvaluationMatrixAt ⟨6, by decide⟩)
        (incomingBeforeSource.hypercubicAct h) =
      sourcePermutationContribution incomingBeforeSource permutation := by
  dsimp [sourcePermutationContribution]
  rw [incomingBefore_tensorSign_reflection_invariant]
  rw [incomingBefore_action_reflection_invariant]

/-- OUR factorization of a first-source reflection block. -/
theorem incomingBefore_block_factor
    (permutation : Fin 24) :
    sourceReflectionBlock incomingBeforeSource permutation =
      16 * sourcePermutationContribution incomingBeforeSource permutation := by
  unfold sourceReflectionBlock
  simp_rw [incomingBefore_reflection_term]
  norm_num

/- OUR kernel-checked 24-entry table for the first source. -/
set_option maxHeartbeats 3000000 in
theorem incomingBefore_permutation_table
    (permutation : Fin 24) :
    sourcePermutationContribution incomingBeforeSource permutation =
      expectedBeforePermutationContribution permutation := by
  set_option maxRecDepth 100000 in
    fin_cases permutation <;> decide +kernel

/-- OUR action of a fixed unsigned permutation is independent of the
reflection mask on the second source. -/
theorem incomingAfter_action_reflection_invariant
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    incomingAfterSource.hypercubicAct
        (decodedHypercubicCharacterElement permutation reflectionMask) =
      incomingAfterSource.hypercubicAct
        (decodedHypercubicCharacterElement permutation 0) := by
  rfl

/-- OUR transfer of the common decoration's reflection-sign cancellation to
the second source. -/
theorem incomingAfter_tensorSign_reflection_invariant
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    incomingAfterSource.tensorSign
        (decodedHypercubicCharacterElement permutation reflectionMask) =
      incomingAfterSource.tensorSign
        (decodedHypercubicCharacterElement permutation 0) := by
  change incomingBeforeSource.tensorSign
      (decodedHypercubicCharacterElement permutation reflectionMask) =
    incomingBeforeSource.tensorSign
      (decodedHypercubicCharacterElement permutation 0)
  exact incomingBefore_tensorSign_reflection_invariant permutation reflectionMask

/-- OUR factorization of each second-source reflection summand. -/
theorem incomingAfter_reflection_term
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    incomingAfterSource.tensorSign h *
      labeledPlaneTraceEvaluation (encodedEvaluationMatrixAt ⟨6, by decide⟩)
        (incomingAfterSource.hypercubicAct h) =
      sourcePermutationContribution incomingAfterSource permutation := by
  dsimp [sourcePermutationContribution]
  rw [incomingAfter_tensorSign_reflection_invariant]
  rw [incomingAfter_action_reflection_invariant]

/-- OUR factorization of a second-source reflection block. -/
theorem incomingAfter_block_factor
    (permutation : Fin 24) :
    sourceReflectionBlock incomingAfterSource permutation =
      16 * sourcePermutationContribution incomingAfterSource permutation := by
  unfold sourceReflectionBlock
  simp_rw [incomingAfter_reflection_term]
  norm_num

/- OUR kernel-checked 24-entry table for the second source. -/
set_option maxHeartbeats 3000000 in
theorem incomingAfter_permutation_table
    (permutation : Fin 24) :
    sourcePermutationContribution incomingAfterSource permutation =
      expectedAfterPermutationContribution permutation := by
  set_option maxRecDepth 100000 in
    fin_cases permutation <;> decide +kernel

/-- OUR exact finite sum of the first compact permutation table. -/
theorem expectedBeforePermutationContribution_sum :
    ∑ permutation : Fin 24,
      expectedBeforePermutationContribution permutation = 4 := by
  decide +kernel

/-- OUR exact finite sum of the second compact permutation table. -/
theorem expectedAfterPermutationContribution_sum :
    ∑ permutation : Fin 24,
      expectedAfterPermutationContribution permutation = 0 := by
  decide +kernel

/-- OUR full Reynolds value of a literal derivative-free source. -/
def sourceReynoldsTraceValue
    (source : LabeledLocalWordSector 8 0) : ℚ :=
  (1 / 384 : ℚ) * ∑ h : Hypercubic4,
    source.tensorSign h *
      labeledPlaneTraceEvaluation (encodedEvaluationMatrixAt ⟨6, by decide⟩)
        (source.hypercubicAct h)

/-- OUR decomposition of a Reynolds value into its 24 bounded reflection
blocks. -/
theorem sourceReynoldsTraceValue_blocks
    (source : LabeledLocalWordSector 8 0) :
    sourceReynoldsTraceValue source =
      (1 / 384 : ℚ) * ∑ permutation : Fin 24,
        sourceReflectionBlock source permutation := by
  unfold sourceReynoldsTraceValue
  let summand : Hypercubic4 → ℚ := fun h =>
    source.tensorSign h *
      labeledPlaneTraceEvaluation (encodedEvaluationMatrixAt ⟨6, by decide⟩)
        (source.hypercubicAct h)
  change (1 / 384 : ℚ) * ∑ h : Hypercubic4, summand h = _
  calc
    (1 / 384 : ℚ) * ∑ h : Hypercubic4, summand h =
        (1 / 384 : ℚ) * ∑ code : Fin 24 × Fin 16,
          summand (hypercubicCharacterCodeEquiv code) := by
      rw [Equiv.sum_comp hypercubicCharacterCodeEquiv summand]
    _ = (1 / 384 : ℚ) * ∑ permutation : Fin 24,
        sourceReflectionBlock source permutation := by
      simp [summand, hypercubicCharacterCodeEquiv,
        sourceReflectionBlock, Fintype.sum_prod_type]

/-- OUR exact Reynolds value of the first literal source. -/
theorem sourceReynoldsTraceValue_before :
    sourceReynoldsTraceValue incomingBeforeSource = (1 : ℚ) / 6 := by
  rw [sourceReynoldsTraceValue_blocks incomingBeforeSource]
  simp_rw [incomingBefore_block_factor, incomingBefore_permutation_table]
  rw [← Finset.mul_sum, expectedBeforePermutationContribution_sum]
  norm_num

/-- OUR exact Reynolds value of the second literal source. -/
theorem sourceReynoldsTraceValue_after :
    sourceReynoldsTraceValue incomingAfterSource = 0 := by
  rw [sourceReynoldsTraceValue_blocks incomingAfterSource]
  simp_rw [incomingAfter_block_factor, incomingAfter_permutation_table]
  rw [← Finset.mul_sum, expectedAfterPermutationContribution_sum]
  norm_num

/-- OUR trace functional before quotienting signed hypercubic-orbit
relations. -/
def rawReynoldsTraceEvaluation (assignment : Fin 98) :
    FieldEightOrbitSpace →ₗ[ℚ] ℚ :=
  (orbitPlaneTraceEvaluationLinear
      (encodedEvaluationMatrixAt assignment) 8 0).comp
    (sectorFieldOrbitReynolds 8 0)

/-- OUR proof that ordinary derivative-free trace rows vanish under the raw
trace functional. -/
theorem rawReynoldsTraceEvaluation_physicalTraceRow_zero
    (assignment : Fin 98) (generator : FieldEightTraceGenerator) :
    rawReynoldsTraceEvaluation assignment
        (fieldEightPhysicalTraceRow generator) = 0 := by
  change orbitPlaneTraceEvaluationLinear
      (encodedEvaluationMatrixAt assignment) 8 0
      (sectorFieldOrbitReynolds 8 0
        (fieldEightPhysicalTraceRow generator)) = 0
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  rw [map_smul, map_sum]
  apply smul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro h _
  rw [fieldEightPhysicalTraceRow_equivariant]
  rw [LinearMap.map_smul]
  rw [fieldEightPhysicalTraceRow_evaluation_zero
    (encodedEvaluationMatrixAt assignment)
    (encodedEvaluationMatrixAt_traceless assignment)]
  simp

/-- OUR proof that signed orbit relations lie in the raw functional's
kernel. -/
theorem signedOrbitRelationSubmodule_le_rawReynoldsKernel
    (assignment : Fin 98) :
    fieldEightSignedOrbitRelationSubmodule ≤
      LinearMap.ker (rawReynoldsTraceEvaluation assignment) := by
  rw [← ker_sectorFieldOrbitReynolds_eq_signedOrbitRelations]
  intro value hvalue
  rw [LinearMap.mem_ker] at hvalue ⊢
  simp [rawReynoldsTraceEvaluation, hvalue]

/-- OUR descent of the trace functional through signed orbit relations. -/
def incomingCoinvariantTraceEvaluation (assignment : Fin 98) :
    FieldEightSignedOrbitCoinvariant →ₗ[ℚ] ℚ :=
  Submodule.liftQ fieldEightSignedOrbitRelationSubmodule
    (rawReynoldsTraceEvaluation assignment)
    (signedOrbitRelationSubmodule_le_rawReynoldsKernel assignment)

/-- OUR proof that ordinary trace rows vanish after signed-orbit descent. -/
theorem incomingCoinvariantTraceEvaluation_physicalTraceRow_zero
    (assignment : Fin 98) (generator : FieldEightTraceGenerator) :
    incomingCoinvariantTraceEvaluation assignment
        (fieldEightCoinvariantTraceRow generator) = 0 := by
  change rawReynoldsTraceEvaluation assignment
      (fieldEightPhysicalTraceRow generator) = 0
  exact rawReynoldsTraceEvaluation_physicalTraceRow_zero assignment generator

/-- OUR inclusion of every ordinary trace relation in the descended
functional's kernel. -/
theorem physicalTraceRelationSubmodule_le_incomingKernel
    (assignment : Fin 98) :
    fieldEightPhysicalTraceRelationSubmodule ≤
      LinearMap.ker (incomingCoinvariantTraceEvaluation assignment) := by
  rw [fieldEightPhysicalTraceRelationSubmodule, Submodule.span_le]
  rintro _ ⟨generator, rfl⟩
  exact incomingCoinvariantTraceEvaluation_physicalTraceRow_zero
    assignment generator

/-- OUR descent of the trace functional through every ordinary
derivative-free trace relation. -/
def incomingQuotientTraceEvaluation (assignment : Fin 98) :
    FieldEightPhysicalTraceQuotient →ₗ[ℚ] ℚ :=
  Submodule.liftQ fieldEightPhysicalTraceRelationSubmodule
    (incomingCoinvariantTraceEvaluation assignment)
    (physicalTraceRelationSubmodule_le_incomingKernel assignment)

/-- OUR signed difference of the two literal source orbits. -/
def literalIncomingCommutatorVector : FieldEightOrbitSpace :=
  -Finsupp.single (Quotient.mk _ incomingBeforeSource) 1 +
    Finsupp.single (Quotient.mk _ incomingAfterSource) 1

/-- OUR image of the literal signed difference in the signed orbit quotient. -/
def literalIncomingCommutatorCoinvariant : FieldEightSignedOrbitCoinvariant :=
  Submodule.Quotient.mk literalIncomingCommutatorVector

/-- OUR image of the literal signed difference in the ordinary
derivative-free trace quotient. -/
def literalIncomingCommutatorClass : FieldEightPhysicalTraceQuotient :=
  Submodule.Quotient.mk literalIncomingCommutatorCoinvariant

/-- OUR evaluation formula for one field-orbit basis vector. -/
theorem rawReynoldsTraceEvaluation_single
    (assignment : Fin 98) (target : FieldEightOrbitCarrier) :
    rawReynoldsTraceEvaluation assignment (Finsupp.single target 1) =
      (1 / 384 : ℚ) * ∑ h : Hypercubic4,
        target.tensorSign h *
          orbitPlaneTraceEvaluation (encodedEvaluationMatrixAt assignment)
            (target.hypercubicAct h) := by
  change orbitPlaneTraceEvaluationLinear
      (encodedEvaluationMatrixAt assignment) 8 0
      (sectorFieldOrbitReynolds 8 0 (Finsupp.single target 1)) = _
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  rw [map_smul, map_sum]
  simp only [signedSectorFieldOrbitAction_single,
    orbitPlaneTraceEvaluationLinear_single, one_mul, smul_eq_mul]

/-- OUR exact nonzero evaluation of the literal signed incoming vector. -/
theorem rawReynoldsTraceEvaluation_literalIncoming :
    rawReynoldsTraceEvaluation ⟨6, by decide⟩
        literalIncomingCommutatorVector = -(1 : ℚ) / 6 := by
  unfold literalIncomingCommutatorVector
  simp only [LinearMap.map_add, LinearMap.map_neg]
  rw [rawReynoldsTraceEvaluation_single,
    rawReynoldsTraceEvaluation_single]
  simp only [FieldRelabelOrbitCarrier.tensorSign_mk,
    FieldRelabelOrbitCarrier.hypercubicAct_mk,
    orbitPlaneTraceEvaluation_mk]
  change -sourceReynoldsTraceValue incomingBeforeSource +
      sourceReynoldsTraceValue incomingAfterSource = _
  rw [sourceReynoldsTraceValue_before, sourceReynoldsTraceValue_after]
  norm_num

/-- OUR quotient-evaluation formula for the literal incoming class. -/
theorem incomingQuotientTraceEvaluation_literalIncoming :
    incomingQuotientTraceEvaluation ⟨6, by decide⟩
        literalIncomingCommutatorClass =
      rawReynoldsTraceEvaluation ⟨6, by decide⟩
        literalIncomingCommutatorVector := by
  rfl

/-- OUR certificate that the literal incoming class survives every ordinary
derivative-free trace relation. -/
theorem literalIncomingCommutatorClass_ne_zero :
    literalIncomingCommutatorClass ≠ 0 := by
  intro hzero
  have hvalue := incomingQuotientTraceEvaluation_literalIncoming
  rw [rawReynoldsTraceEvaluation_literalIncoming] at hvalue
  rw [hzero, LinearMap.map_zero] at hvalue
  norm_num at hvalue

#print axioms sourceReynoldsTraceValue_before
#print axioms sourceReynoldsTraceValue_after
#print axioms literalIncomingCommutatorClass_ne_zero

end HypercubicDimension16IncomingCommutatorTraceCertificate
end YangMills
end QuantumTheory
end Mettapedia
