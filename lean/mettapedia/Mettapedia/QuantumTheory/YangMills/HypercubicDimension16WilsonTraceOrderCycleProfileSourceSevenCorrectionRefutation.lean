import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldEightTracePhysicalCompleteness
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch

/-!
# OUR source-seven refutation of the present one-class correction

The preceding certificate supplies a second actual source-seven
covariant-commutator row and a bounded ordinary-trace quotient functional.
This module connects that finite evidence to OUR present cycle-profile
correction.  The functional kills the one fixed incoming class used by every
seven-field compensator, but it detects the secondary row's distinct
eight-field component.  Thus the current one-class correction cannot descend
through all physical source-seven commutator rows.

This is a refutation of a particular OUR correction family, not a claim that
no multi-class correction or Wilson-functional construction can repair the
remaining source-seven band.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenCorrectionRefutation

open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationBlocks
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16AntisymmetryQuotient
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch

/-- OUR field-eight cast is judgmentally trivial when the exact index is the
literal eight. -/
theorem our_exactFieldEightOrbitCast_literal
    (orbit : FieldEightOrbitCarrier) (h : (8 : Fin 9) = ourEightFieldCount) :
    exactFieldEightOrbitCast (8 : Fin 9) h orbit = orbit := by
  cases h
  exact exactFieldEightOrbitCast_self orbit rfl

/-- OUR ordinary eight-field projection of the secondary physical component
is its literal signed pair. -/
theorem exactFieldEightProjection_ourSecondaryCommutator_fieldEight
    (policy : PhysicalRelationPolicy) :
    exactFieldEightProjection
      (orbitFieldFilter (fun fieldCount => fieldCount.1 = 8)
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1))) =
      ourSecondaryCommutatorVector := by
  rw [orbitPhysicalRelationOperator_ourSecondaryCommutator_fieldEight_literal]
  simp only [LinearMap.map_add, LinearMap.map_neg,
    exactFieldEightProjection_single, one_smul]
  change
    -Finsupp.single
        (exactFieldEightOrbitCast (8 : Fin 9) (by decide)
          (Quotient.mk _ ourSecondaryBeforeSource)) 1 +
      Finsupp.single
        (exactFieldEightOrbitCast (8 : Fin 9) (by decide)
          (Quotient.mk _ ourSecondaryAfterSource)) 1 =
    ourSecondaryCommutatorVector
  rw [our_exactFieldEightOrbitCast_literal,
    our_exactFieldEightOrbitCast_literal]
  rfl

/-- OUR canonical trace projection of the secondary physical commutator is
the nonzero secondary trace class. -/
theorem exactFieldEightTraceProjection_ourSecondaryCommutator
    (policy : PhysicalRelationPolicy) :
    exactFieldEightTraceProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
      ourSecondaryCommutatorClass := by
  unfold exactFieldEightTraceProjection
  change exactFieldEightTraceClassMap
      (exactFieldEightProjection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1))) = _
  rw [← exactFieldEightProjection_fieldEight_filter]
  rw [exactFieldEightProjection_ourSecondaryCommutator_fieldEight]
  rfl

/-- OUR selected quotient functional sees every present seven-field
compensator channel as zero, so it isolates the canonical eight-field trace
projection in the current profile correction. -/
theorem incomingQuotientTraceEvaluation_cycleProfileCorrection
    (value : ExactFieldRelabelOrbitSpace) :
    incomingQuotientTraceEvaluation ⟨2, by decide⟩
      (ourCycleProfileInvariantTraceOrderCorrection value) =
      -incomingQuotientTraceEvaluation ⟨2, by decide⟩
        (exactFieldEightTraceProjection value) := by
  unfold ourCycleProfileInvariantTraceOrderCorrection
    ourTraceCycleProfileInvariantTraceContribution
    ourThreeCoordinateInvariantTraceOrderCorrection
    ourThirdInvariantTraceContribution
    ourTwoCoordinateInvariantTraceOrderCorrection
    ourTwoCoordinateInvariantSevenTraceCompensator
  simp only [LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply,
    LinearMap.map_add, LinearMap.map_sub, LinearMap.map_smul,
    incomingQuotientTraceEvaluation_literalIncoming_assignmentTwo,
    smul_zero, sub_zero, zero_sub]
  abel

/-- OUR exact nonzero quotient-functional value of the full present
correction on the secondary physical source-seven row. -/
theorem incomingQuotientTraceEvaluation_cycleProfileCorrection_ourSecondaryCommutator
    (policy : PhysicalRelationPolicy) :
    incomingQuotientTraceEvaluation ⟨2, by decide⟩
      (ourCycleProfileInvariantTraceOrderCorrection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1))) =
      (4 : ℚ) / 3 := by
  rw [incomingQuotientTraceEvaluation_cycleProfileCorrection,
    exactFieldEightTraceProjection_ourSecondaryCommutator,
    incomingQuotientTraceEvaluation_ourSecondaryCommutator,
    rawReynoldsTraceEvaluation_ourSecondaryCommutatorVector]
  norm_num

/-- OUR current one-class profile correction does not annihilate the
secondary physical source-seven covariant-commutator row.  This exact
refutation does not make a completeness claim for a revised multi-class
correction. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_ourSecondaryCommutator_ne_zero
    (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) ≠ 0 := by
  intro hzero
  have hvalue := incomingQuotientTraceEvaluation_cycleProfileCorrection_ourSecondaryCommutator
    policy
  rw [hzero, LinearMap.map_zero] at hvalue
  norm_num at hvalue

#print axioms exactFieldEightProjection_ourSecondaryCommutator_fieldEight
#print axioms exactFieldEightTraceProjection_ourSecondaryCommutator
#print axioms incomingQuotientTraceEvaluation_cycleProfileCorrection
#print axioms incomingQuotientTraceEvaluation_cycleProfileCorrection_ourSecondaryCommutator
#print axioms ourCycleProfileInvariantTraceOrderCorrection_ourSecondaryCommutator_ne_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenCorrectionRefutation
