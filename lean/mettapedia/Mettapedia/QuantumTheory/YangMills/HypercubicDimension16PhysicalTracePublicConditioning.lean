import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceQuotient

/-!
# Exact duals and conditioning in the genuine Reynolds normalization

The stored `98 x 98` matrix is the unsigned sum over the `24` coordinate
permutations.  Ordinary trace evaluation of the genuine `384`-element
Reynolds basis is that stored matrix divided by `24`.  Hence the public dual
matrix is `24` times the stored inverse.  This file constructs those quotient
duals and records their sharp row-`l1` analysis constant.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTracePublicConditioning

open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16PhysicalTraceEvaluationData
open HypercubicDimension16PhysicalTraceEvaluationExecutable
open HypercubicDimension16PhysicalTraceConditioningExecutable
open HypercubicDimension16PhysicalTraceEvaluationCertificate
open HypercubicDimension16PhysicalTraceEvaluationReynolds
open HypercubicDimension16PhysicalTraceQuotient

/-- Exact inverse coefficient for the genuinely normalized public evaluation
matrix. -/
def publicEvaluationInverse (row assignment : Fin 98) : ℚ :=
  24 * decodedEvaluationInverse row assignment

/-- The public inverse is an exact left inverse of the matrix `M / 24`. -/
theorem publicEvaluationInverse_replay (row column : Fin 98) :
    (∑ assignment : Fin 98,
      publicEvaluationInverse row assignment *
        (expectedUnsignedEvaluation assignment column / 24)) =
      if row = column then 1 else 0 := by
  simp only [publicEvaluationInverse]
  calc
    (∑ assignment : Fin 98,
        (24 * decodedEvaluationInverse row assignment) *
          (expectedUnsignedEvaluation assignment column / 24)) =
        ∑ assignment : Fin 98,
          decodedEvaluationInverse row assignment *
            expectedUnsignedEvaluation assignment column := by
      apply Finset.sum_congr rfl
      intro assignment _
      ring
    _ = if row = column then 1 else 0 :=
      evaluationInverse_replay row column

/-- Ordinary trace evaluation descends through every standard trace row. -/
def quotientTraceEvaluation (assignment : Fin 98) :
    FieldEightPhysicalTraceQuotient →ₗ[ℚ] ℚ :=
  Submodule.liftQ fieldEightPhysicalTraceRelationSubmodule
    (coinvariantTraceEvaluation assignment)
    (physicalTraceRelationSubmodule_le_evaluationKernel assignment)

@[simp] theorem quotientTraceEvaluation_mk
    (assignment : Fin 98) (value : FieldEightSignedOrbitCoinvariant) :
    quotientTraceEvaluation assignment (Submodule.Quotient.mk value) =
      coinvariantTraceEvaluation assignment value := by
  rfl

/-- Exact coefficient dual on the derivative-free eight-field standard trace
quotient. -/
def physicalTraceCoefficientDual (row : Fin 98) :
    FieldEightPhysicalTraceQuotient →ₗ[ℚ] ℚ :=
  ∑ assignment : Fin 98,
    publicEvaluationInverse row assignment •
      quotientTraceEvaluation assignment

/-- The constructed duals are exactly biorthogonal to the certified free
classes. -/
theorem physicalTraceCoefficientDual_freeClass (row column : Fin 98) :
    physicalTraceCoefficientDual row (physicalTraceFreeClass column) =
      if row = column then 1 else 0 := by
  simp only [physicalTraceCoefficientDual, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, physicalTraceFreeClass,
    quotientTraceEvaluation_mk, coinvariantTraceEvaluation_basis]
  exact publicEvaluationInverse_replay row column

/-- The explicit evaluation dual is exactly the coordinate functional of the
honest quotient basis. -/
theorem physicalTraceCoefficientDual_eq_coord (row : Fin 98) :
    physicalTraceCoefficientDual row = physicalTraceFreeBasis.coord row := by
  apply Module.Basis.ext physicalTraceFreeBasis
  intro column
  rw [physicalTraceFreeBasis_apply,
    physicalTraceCoefficientDual_freeClass]
  rw [← physicalTraceFreeBasis_apply column]
  rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
  simp [eq_comm]

/-- Reconstruction from the exact quotient coordinates. -/
theorem physicalTraceFreeBasis_reconstruction
    (value : FieldEightPhysicalTraceQuotient) :
    (∑ row : Fin 98,
      physicalTraceCoefficientDual row value •
        physicalTraceFreeClass row) = value := by
  simp_rw [physicalTraceCoefficientDual_eq_coord,
    ← physicalTraceFreeBasis_apply]
  exact physicalTraceFreeBasis.sum_repr value

/-- Row-`l1` cost of the genuinely normalized public dual matrix. -/
def publicEvaluationInverseRowL1 (row : Fin 98) : ℚ :=
  ∑ assignment : Fin 98, |publicEvaluationInverse row assignment|

theorem publicEvaluationInverseRowL1_eq (row : Fin 98) :
    publicEvaluationInverseRowL1 row =
      24 * decodedEvaluationInverseRowL1 row := by
  unfold publicEvaluationInverseRowL1 publicEvaluationInverse
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro assignment _
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 24)]
  have hdenominator :
      (encodedEvaluationInverseFraction row assignment).2 > 0 := by
    decide +kernel +revert
  rw [← decodedEvaluationInverseAbs_eq_abs row assignment hdenominator]

/-- Sharp public coefficient-sup analysis constant. -/
def publicEvaluationConditioningConstant : ℚ :=
  14739388451343 / 30664304

theorem publicEvaluationConditioningConstant_eq_raw :
    publicEvaluationConditioningConstant =
      24 * evaluationInverseConditioningConstant := by
  norm_num [publicEvaluationConditioningConstant,
    evaluationInverseConditioningConstant]

theorem publicEvaluationInverseRowL1_le_real (row : Fin 98) :
    (publicEvaluationInverseRowL1 row : ℝ) ≤
      (publicEvaluationConditioningConstant : ℝ) := by
  rw [publicEvaluationInverseRowL1_eq,
    publicEvaluationConditioningConstant_eq_raw]
  push_cast
  exact mul_le_mul_of_nonneg_left
    (by
      simpa [evaluationInverseConditioningConstant] using
        evaluationInverse_row_l1_le_real row)
    (by norm_num)

/-- Row `30` attains the public constant exactly. -/
theorem publicEvaluationInverseRowL1_attained :
    publicEvaluationInverseRowL1 ⟨30, by decide⟩ =
      publicEvaluationConditioningConstant := by
  rw [publicEvaluationInverseRowL1_eq,
    evaluationInverse_row_l1_attained,
    publicEvaluationConditioningConstant_eq_raw]

end HypercubicDimension16PhysicalTracePublicConditioning
end YangMills
end QuantumTheory
end Mettapedia
