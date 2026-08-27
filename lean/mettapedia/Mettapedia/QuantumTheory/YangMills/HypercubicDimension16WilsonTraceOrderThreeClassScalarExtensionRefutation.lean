import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepairTracelessRefutation

/-!
# OUR scalar-literal extension refutation

The second singleton-trace witness does more than refute one chosen scalar
combination.  The separating quotient functional kills
`literalIncomingCommutatorClass` itself.  Consequently no scalar-valued
functional, regardless of how it is constructed, can repair the witness when
it is attached only to that literal quotient direction.

This closes OUR full scalar-literal extension family over the fixed three-class
base.  A subsequent repair must alter a non-literal quotient direction or the
base map itself.  This result does not refute arbitrary quotient-valued
coordinate families or a semantics-preserving canonical `(F,D)` descent.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderThreeClassScalarExtensionRefutation

open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepair
open HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepair
open HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepairTracelessRefutation

/-- OUR full scalar-literal extension family over the fixed three-class map.
The parameter is deliberately arbitrary: it need not arise from a preselected
coordinate list. -/
def ourThreeClassScalarLiteralExtension
    (scalar : ExactFieldRelabelOrbitSpace →ₗ[ℚ] ℚ) :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ourThreeClassSourceSevenTraceOrderCorrection +
    scalar.smulRight literalIncomingCommutatorClass

/-- The existing six-scalar map is one member of OUR arbitrary scalar-literal
extension family. -/
theorem ourParameterSynthesizedSourceSevenTraceOrderCorrection_eq_scalarExtension :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection =
      ourThreeClassScalarLiteralExtension ourExistingScalarNullDirection :=
  rfl

/-- The witness has the same exact quotient-functional value for every
scalar-literal extension because the functional annihilates the entire added
literal direction. -/
theorem incomingQuotientTraceEvaluation_scalarExtension_ourSecondIBPSingletonTrace
    (scalar : ExactFieldRelabelOrbitSpace →ₗ[ℚ] ℚ)
    (policy : PhysicalRelationPolicy) :
    incomingQuotientTraceEvaluation ⟨2, by decide⟩
      (ourThreeClassScalarLiteralExtension scalar
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourSecondIBPSingletonTraceGenerator policy) 1))) =
      -(4 : ℚ) / 3 := by
  unfold ourThreeClassScalarLiteralExtension
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.map_add, LinearMap.map_smul,
    incomingQuotientTraceEvaluation_threeClassCorrection_ourSecondIBPSingletonTrace,
    incomingQuotientTraceEvaluation_literalIncoming_assignmentTwo,
    smul_zero, add_zero]

theorem ourThreeClassScalarLiteralExtension_ourSecondIBPSingletonTrace_ne_zero
    (scalar : ExactFieldRelabelOrbitSpace →ₗ[ℚ] ℚ)
    (policy : PhysicalRelationPolicy) :
    ourThreeClassScalarLiteralExtension scalar
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondIBPSingletonTraceGenerator policy) 1)) ≠ 0 := by
  intro hzero
  have hvalue :=
    incomingQuotientTraceEvaluation_scalarExtension_ourSecondIBPSingletonTrace
      scalar policy
  rw [hzero, LinearMap.map_zero] at hvalue
  norm_num at hvalue

/-- No member of OUR arbitrary scalar-literal extension family descends
through the full physical-relation submodule under either policy. -/
theorem ourThreeClassScalarLiteralExtension_not_descends
    (scalar : ExactFieldRelabelOrbitSpace →ₗ[ℚ] ℚ)
    (policy : PhysicalRelationPolicy) :
    ¬ orbitPhysicalRelationSubmodule policy ≤
      LinearMap.ker (ourThreeClassScalarLiteralExtension scalar) := by
  intro hdescent
  have hmember :
      orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondIBPSingletonTraceGenerator policy) 1) ∈
        orbitPhysicalRelationSubmodule policy :=
    ⟨Finsupp.single (ourSecondIBPSingletonTraceGenerator policy) 1, rfl⟩
  have hzero := LinearMap.mem_ker.mp (hdescent hmember)
  exact ourThreeClassScalarLiteralExtension_ourSecondIBPSingletonTrace_ne_zero
    scalar policy hzero

#print axioms incomingQuotientTraceEvaluation_scalarExtension_ourSecondIBPSingletonTrace
#print axioms ourThreeClassScalarLiteralExtension_not_descends

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderThreeClassScalarExtensionRefutation
