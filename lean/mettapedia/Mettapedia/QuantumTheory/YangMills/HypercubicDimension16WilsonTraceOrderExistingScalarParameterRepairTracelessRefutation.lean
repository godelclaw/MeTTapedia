import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepair

/-!
# OUR source-seven traceless refutation of the existing-scalar repair

The six-scalar deformation repairs the first displayed singleton-trace row,
but it must vanish on every actual physical relation before it can descend.
This module constructs a second actual singleton-trace relation: retain the
nondegenerate derivative geometry of OUR second-IBP carrier and impose a
genuine one-letter trace at field `0`.

Its exact signed `H(4)` weights make the third IBP coordinate zero and the
secondary plane-profile coordinate one.  The quotient functional already
used to separate the secondary source-seven residual annihilates the literal
incoming class but evaluates that residual as `4 / 3`.  Hence it evaluates
OUR existing-scalar repair on this actual relation as `-4 / 3`, under either
physical policy.

This is a machine-checked refutation of this particular six-scalar repair.
It does not refute a larger coordinate family, a semantics-preserving
canonical `(F,D)` descent, joint rank or conditioning, nor the Yang--Mills
mass-gap programme.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepairTracelessRefutation

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open SU2LatticeFDCensusNoGo
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16IBPTraceRelations
open HypercubicDimension16SU2TraceRelations
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16AntisymmetryQuotient
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationBlocks
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderInvariantBianchi
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair
open HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenCorrectionRefutation
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassCompatibility
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation
open HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepair

/-- OUR second singleton-trace carrier retains the independent two-derivative
geometry of the second-IBP calibration while making field `0` a genuine
one-letter trace. -/
abbrev ourSecondIBPSingletonTraceCarrier : RelationCarrier :=
  setTraceOrder ourSecondIBPCarrier ourSingletonTraceOrder

theorem ourSecondIBPSingletonTraceCarrier_singleton :
    IsSingletonTrace ourSecondIBPSingletonTraceCarrier ⟨0, by decide⟩ := by
  change ourSingletonTraceOrder (0 : Fin 7) = 0
  decide +kernel

/-- OUR actual physical tracelessness relation on the displayed carrier. -/
def ourSecondIBPSingletonTraceGenerator
    (policy : PhysicalRelationPolicy) : PhysicalRelationGenerator policy :=
  .traceless ourSecondIBPSingletonTraceCarrier ⟨0, by decide⟩
    ourSecondIBPSingletonTraceCarrier_singleton

abbrev ourSecondIBPSingletonTraceLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData ourSecondIBPSingletonTraceCarrier.2)

abbrev ourSecondIBPSingletonTraceOrbit : FieldSevenOrbitCarrier :=
  Quotient.mk _ ourSecondIBPSingletonTraceLabeled

def ourSecondIBPSingletonTraceExactTarget : ExactFieldRelabelOrbitCarrier :=
  exactFieldRelabelOrbitOfOriented
    (exactNormalizedSectorData ourSecondIBPSingletonTraceCarrier)

theorem ourSecondIBPSingletonTraceExactTarget_eq_seven :
    ourSecondIBPSingletonTraceExactTarget =
      (⟨ourSevenFieldCount, ourSecondIBPSingletonTraceOrbit⟩ :
        ExactFieldRelabelOrbitCarrier) := rfl

theorem ourSecondIBPSingletonTrace_orientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment ourSecondIBPSingletonTraceCarrier.2) = 1 := by
  decide +kernel

theorem ourNormalizeExactContextualBasis_ourSecondIBPSingletonTrace :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis ourSecondIBPSingletonTraceCarrier) =
      Finsupp.single ourSecondIBPSingletonTraceExactTarget 1 := by
  unfold normalizeExactContextualBasis
  rw [LinearMap.map_smul, normalizeExactFieldRelabel_single]
  unfold normalizeExactFieldRelabelBasis
  rw [ourSecondIBPSingletonTrace_orientationCoefficient]
  simp [ourSecondIBPSingletonTraceExactTarget]

theorem orbitPhysicalRelationOperator_ourSecondIBPSingletonTrace
    (policy : PhysicalRelationPolicy) :
    orbitPhysicalRelationOperator policy
      (Finsupp.single (ourSecondIBPSingletonTraceGenerator policy) 1) =
        Finsupp.single ourSecondIBPSingletonTraceExactTarget 1 := by
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  simp only [one_smul, physicalRelationRow,
    ourSecondIBPSingletonTraceGenerator, tracelessLetterRow]
  rw [normalizeExactContextual_single]
  simp only [one_smul]
  exact ourNormalizeExactContextualBasis_ourSecondIBPSingletonTrace

/-! ## Bounded signed-orbit certificates -/

set_option maxRecDepth 100000 in
theorem ourSecondIBPSingletonTrace_thirdIBPAxisPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourSecondIBPSingletonTraceLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourSecondIBPSingletonTraceLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourSecondIBPSingletonTrace_secondaryPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourSecondIBPSingletonTraceLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2)
          (ourSecondIBPSingletonTraceLabeled.hypercubicAct h) : ℚ)) = 16 := by
  decide +kernel

theorem exactFieldSevenProjection_ourSecondIBPSingletonTrace
    (policy : PhysicalRelationPolicy) :
    exactFieldSevenProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondIBPSingletonTraceGenerator policy) 1)) =
      Finsupp.single ourSecondIBPSingletonTraceOrbit 1 := by
  rw [orbitPhysicalRelationOperator_ourSecondIBPSingletonTrace,
    ourSecondIBPSingletonTraceExactTarget_eq_seven]
  exact exactFieldSevenProjection_sevenTarget_single
    ourSecondIBPSingletonTraceOrbit 1

theorem exactFieldEightTraceProjection_ourSecondIBPSingletonTrace_zero
    (policy : PhysicalRelationPolicy) :
    exactFieldEightTraceProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondIBPSingletonTraceGenerator policy) 1)) = 0 := by
  unfold exactFieldEightTraceProjection
  simp only [LinearMap.comp_apply]
  rw [orbitPhysicalRelationOperator_ourSecondIBPSingletonTrace,
    ourSecondIBPSingletonTraceExactTarget_eq_seven,
    exactFieldEightProjection_sevenTarget_single]
  simp

set_option maxRecDepth 100000 in
theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourSecondIBPSingletonTrace :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSecondIBPSingletonTraceOrbit (1 : ℚ))) = 0 := by
  change ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourSecondIBPSingletonTraceLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourThirdIBPAxisPlanePairCoordinate_reynolds_single
    ourSecondIBPSingletonTraceLabeled 0
    ourSecondIBPSingletonTrace_thirdIBPAxisPlanePairSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourSecondIBPSingletonTrace :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSecondIBPSingletonTraceOrbit (1 : ℚ))) = 1 / 24 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourSecondIBPSingletonTraceLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 1 / 24
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 0 2) ourSecondIBPSingletonTraceLabeled 16
    ourSecondIBPSingletonTrace_secondaryPlaneProfileSignedWeight]
  norm_num

theorem ourInvariantThirdIBPAxisCoordinate_ourSecondIBPSingletonTrace_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantThirdIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondIBPSingletonTraceGenerator policy) 1)) = 0 := by
  unfold ourInvariantThirdIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSecondIBPSingletonTrace,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourSecondIBPSingletonTrace]
  norm_num

theorem ourSecondaryPlaneProfileInvariantCoordinate_ourSecondIBPSingletonTrace
    (policy : PhysicalRelationPolicy) :
    ourSecondaryPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondIBPSingletonTraceGenerator policy) 1)) = 1 := by
  unfold ourSecondaryPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSecondIBPSingletonTrace,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourSecondIBPSingletonTrace]
  norm_num

/-! ## Quotient-functional refutation -/

theorem incomingQuotientTraceEvaluation_cycleProfileCorrection_ourSecondIBPSingletonTrace_zero
    (policy : PhysicalRelationPolicy) :
    incomingQuotientTraceEvaluation ⟨2, by decide⟩
      (ourCycleProfileInvariantTraceOrderCorrection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourSecondIBPSingletonTraceGenerator policy) 1))) = 0 := by
  rw [incomingQuotientTraceEvaluation_cycleProfileCorrection,
    exactFieldEightTraceProjection_ourSecondIBPSingletonTrace_zero]
  simp

theorem incomingQuotientTraceEvaluation_ourSecondarySourceSevenResidual :
    incomingQuotientTraceEvaluation ⟨2, by decide⟩
      ourSecondarySourceSevenResidual = (4 : ℚ) / 3 := by
  unfold ourSecondarySourceSevenResidual
  exact incomingQuotientTraceEvaluation_cycleProfileCorrection_ourSecondaryCommutator
    .offShell

theorem incomingQuotientTraceEvaluation_threeClassCorrection_ourSecondIBPSingletonTrace
    (policy : PhysicalRelationPolicy) :
    incomingQuotientTraceEvaluation ⟨2, by decide⟩
      (ourThreeClassSourceSevenTraceOrderCorrection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourSecondIBPSingletonTraceGenerator policy) 1))) =
      -(4 : ℚ) / 3 := by
  unfold ourThreeClassSourceSevenTraceOrderCorrection
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smulRight_apply, LinearMap.map_add, LinearMap.map_sub,
    LinearMap.map_smul]
  rw [incomingQuotientTraceEvaluation_cycleProfileCorrection_ourSecondIBPSingletonTrace_zero,
    ourSecondaryPlaneProfileInvariantCoordinate_ourSecondIBPSingletonTrace,
    ourInvariantThirdIBPAxisCoordinate_ourSecondIBPSingletonTrace_zero,
    incomingQuotientTraceEvaluation_ourSecondarySourceSevenResidual]
  norm_num

/-- The displayed quotient functional sees the exact nonzero value
`-4 / 3` of OUR six-scalar repair on the second singleton-trace relation. -/
theorem incomingQuotientTraceEvaluation_existingScalarRepair_ourSecondIBPSingletonTrace
    (policy : PhysicalRelationPolicy) :
    incomingQuotientTraceEvaluation ⟨2, by decide⟩
      (ourParameterSynthesizedSourceSevenTraceOrderCorrection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourSecondIBPSingletonTraceGenerator policy) 1))) =
      -(4 : ℚ) / 3 := by
  unfold ourParameterSynthesizedSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.map_add, LinearMap.map_smul,
    incomingQuotientTraceEvaluation_threeClassCorrection_ourSecondIBPSingletonTrace,
    incomingQuotientTraceEvaluation_literalIncoming_assignmentTwo,
    smul_zero, add_zero]

theorem ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSecondIBPSingletonTrace_ne_zero
    (policy : PhysicalRelationPolicy) :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondIBPSingletonTraceGenerator policy) 1)) ≠ 0 := by
  intro hzero
  have hvalue :=
    incomingQuotientTraceEvaluation_existingScalarRepair_ourSecondIBPSingletonTrace
      policy
  rw [hzero, LinearMap.map_zero] at hvalue
  norm_num at hvalue

/-- Consequently OUR current six-scalar map cannot descend through the full
physical-relation submodule for either physical relation policy. -/
theorem ourParameterSynthesizedSourceSevenTraceOrderCorrection_not_descends
    (policy : PhysicalRelationPolicy) :
    ¬ orbitPhysicalRelationSubmodule policy ≤
      LinearMap.ker ourParameterSynthesizedSourceSevenTraceOrderCorrection := by
  intro hdescent
  have hmember :
      orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondIBPSingletonTraceGenerator policy) 1) ∈
        orbitPhysicalRelationSubmodule policy :=
    ⟨Finsupp.single (ourSecondIBPSingletonTraceGenerator policy) 1, rfl⟩
  have hzero := LinearMap.mem_ker.mp (hdescent hmember)
  exact
    ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSecondIBPSingletonTrace_ne_zero
      policy hzero

theorem ourSecondIBPSingletonTrace_sourceFieldCount :
    physicalRelationGeneratorSourceFieldCount
      (ourSecondIBPSingletonTraceGenerator .offShell) = ourSevenFieldCount := by
  rfl

#print axioms ourSecondIBPSingletonTrace_thirdIBPAxisPlanePairSignedWeight
#print axioms ourSecondIBPSingletonTrace_secondaryPlaneProfileSignedWeight
#print axioms orbitPhysicalRelationOperator_ourSecondIBPSingletonTrace
#print axioms incomingQuotientTraceEvaluation_existingScalarRepair_ourSecondIBPSingletonTrace
#print axioms ourParameterSynthesizedSourceSevenTraceOrderCorrection_not_descends

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepairTracelessRefutation
