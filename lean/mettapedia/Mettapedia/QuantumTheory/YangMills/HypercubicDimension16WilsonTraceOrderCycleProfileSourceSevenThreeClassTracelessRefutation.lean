import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepair

/-!
# OUR singleton-trace refutation of the three-class source-seven repair

The preceding three-class coordinate repair cancels two explicit
source-seven covariant-commutator rows and selected differential and trace
rows. This module tests a different actual relation type: a seven-field
carrier with the same two-derivative word as the incoming commutator, but
with one field in a genuine singleton trace. The associated physical
tracelessness relation is available under both policies.

The signed-hypercubic replay has exact weights 32, 0, 0, and -96/5 for the
original derivative, IBP, third, and cycle-profile coordinates; both new
plane-profile selectors vanish. The complete three-class map therefore
takes the exact value (-1/10) times literalIncomingCommutatorClass on this
relation. Since that class is already certified nonzero, the map cannot
descend through the complete physical relation submodule under either policy.

This is OUR explicit mismatch theorem for this particular three-class
extension with its cycle-profile base held fixed. It does not rule out a
reparameterization that also changes that base, a further extension with
additional coordinates, nor does it provide a complete source-seven census,
joint rank, conditioning, or Wilson-functional coordinates.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation

open V14HypercubicFDCensus
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
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16FieldEightPhysicalTrace
open SU2LatticeFDCensusNoGo
open V14HypercubicQuarticCensus
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderInvariantBianchi
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair
open HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassCompatibility
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepair
open HypercubicDimension16IncomingCommutatorTraceMismatch

abbrev ourSingletonTraceOrder : Equiv.Perm (Fin 7) :=
  (ourFieldSevenCommutatorCarrier.2.trace.traceOrder).trans
    (Equiv.swap (0 : Fin 7) 1)

abbrev ourSingletonTraceCarrier : RelationCarrier :=
  setTraceOrder ourFieldSevenCommutatorCarrier ourSingletonTraceOrder

theorem ourSingletonTraceCarrier_singleton :
    IsSingletonTrace ourSingletonTraceCarrier ⟨0, by decide⟩ := by
  change ourSingletonTraceOrder (0 : Fin 7) = 0
  decide +kernel

def ourSingletonTraceGenerator
    (policy : PhysicalRelationPolicy) : PhysicalRelationGenerator policy :=
  .traceless ourSingletonTraceCarrier ⟨0, by decide⟩
    ourSingletonTraceCarrier_singleton

abbrev ourSingletonTraceLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData ourSingletonTraceCarrier.2)

abbrev ourSingletonTraceOrbit : FieldSevenOrbitCarrier :=
  Quotient.mk _ ourSingletonTraceLabeled

def ourSingletonTraceExactTarget : ExactFieldRelabelOrbitCarrier :=
  exactFieldRelabelOrbitOfOriented
    (exactNormalizedSectorData ourSingletonTraceCarrier)

theorem ourSingletonTraceExactTarget_eq_seven :
    ourSingletonTraceExactTarget =
      (⟨ourSevenFieldCount, ourSingletonTraceOrbit⟩ :
        ExactFieldRelabelOrbitCarrier) := rfl

theorem ourSingletonTrace_orientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment ourSingletonTraceCarrier.2) = 1 := by
  decide +kernel

theorem ourNormalizeExactContextualBasis_ourSingletonTrace :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis ourSingletonTraceCarrier) =
      Finsupp.single ourSingletonTraceExactTarget 1 := by
  unfold normalizeExactContextualBasis
  rw [LinearMap.map_smul, normalizeExactFieldRelabel_single]
  unfold normalizeExactFieldRelabelBasis
  rw [ourSingletonTrace_orientationCoefficient]
  simp [ourSingletonTraceExactTarget]

theorem orbitPhysicalRelationOperator_ourSingletonTrace
    (policy : PhysicalRelationPolicy) :
    orbitPhysicalRelationOperator policy
      (Finsupp.single (ourSingletonTraceGenerator policy) 1) =
        Finsupp.single ourSingletonTraceExactTarget 1 := by
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  simp only [one_smul, physicalRelationRow, ourSingletonTraceGenerator,
    tracelessLetterRow]
  rw [normalizeExactContextual_single]
  simp only [one_smul]
  exact ourNormalizeExactContextualBasis_ourSingletonTrace

theorem ourSingletonTrace_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourSingletonTraceLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourSingletonTraceLabeled.hypercubicAct h) : ℚ)) = 32 := by
  decide +kernel

theorem ourSingletonTrace_IBPAxisPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourSingletonTraceLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourSingletonTraceLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

theorem ourSingletonTrace_thirdIBPAxisPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourSingletonTraceLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourSingletonTraceLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

theorem ourSingletonTrace_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourSingletonTraceLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourSingletonTraceLabeled.hypercubicAct h)) = -96 / 5 := by
  decide +kernel

theorem ourSingletonTrace_incomingSelectorSignedWeight :
    (∑ h : Hypercubic4,
      ourSingletonTraceLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3) (ourSingletonTraceLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

theorem ourSingletonTrace_secondarySelectorSignedWeight :
    (∑ h : Hypercubic4,
      ourSingletonTraceLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2) (ourSingletonTraceLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

theorem exactFieldSevenProjection_ourSingletonTrace
    (policy : PhysicalRelationPolicy) :
    exactFieldSevenProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) =
      Finsupp.single ourSingletonTraceOrbit 1 := by
  rw [orbitPhysicalRelationOperator_ourSingletonTrace,
    ourSingletonTraceExactTarget_eq_seven]
  exact exactFieldSevenProjection_sevenTarget_single
    ourSingletonTraceOrbit 1

theorem exactFieldEightTraceProjection_ourSingletonTrace_zero
    (policy : PhysicalRelationPolicy) :
    exactFieldEightTraceProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) = 0 := by
  unfold exactFieldEightTraceProjection
  simp only [LinearMap.comp_apply]
  rw [orbitPhysicalRelationOperator_ourSingletonTrace,
    ourSingletonTraceExactTarget_eq_seven,
    exactFieldEightProjection_sevenTarget_single]
  simp

set_option maxRecDepth 100000 in
theorem derivativeAxisCoordinate_reynolds_ourSingletonTrace :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSingletonTraceOrbit (1 : ℚ))) = 1 / 12 := by
  change ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourSingletonTraceLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 1 / 12
  rw [ourDerivativeAxisCoordinate_reynolds_single ourSingletonTraceLabeled 32
    ourSingletonTrace_signedAxisWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourIBPAxisPlanePairCoordinate_reynolds_ourSingletonTrace :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSingletonTraceOrbit (1 : ℚ))) = 0 := by
  change ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourSingletonTraceLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourIBPAxisPlanePairCoordinate_reynolds_single ourSingletonTraceLabeled 0
    ourSingletonTrace_IBPAxisPlanePairSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourSingletonTrace :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSingletonTraceOrbit (1 : ℚ))) = 0 := by
  change ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourSingletonTraceLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourThirdIBPAxisPlanePairCoordinate_reynolds_single
    ourSingletonTraceLabeled 0
    ourSingletonTrace_thirdIBPAxisPlanePairSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourSingletonTrace :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSingletonTraceOrbit (1 : ℚ))) = -1 / 20 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourSingletonTraceLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = -1 / 20
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourSingletonTraceLabeled (-96 / 5)
    ourSingletonTrace_profileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourDerivativeWordPlanePairCoordinate_reynolds_ourSingletonTrace
    (otherPlane : OrientedPlane)
    (hweight : otherPlane = planeLookup 1 3 ∨ otherPlane = planeLookup 0 2) :
    ourDerivativeWordPlanePairCoordinate otherPlane
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSingletonTraceOrbit (1 : ℚ))) = 0 := by
  rcases hweight with hweight | hweight
  · subst otherPlane
    change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourSingletonTraceLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
    rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
      (planeLookup 1 3) ourSingletonTraceLabeled 0
      ourSingletonTrace_incomingSelectorSignedWeight]
    norm_num
  · subst otherPlane
    change ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourSingletonTraceLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
    rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
      (planeLookup 0 2) ourSingletonTraceLabeled 0
      ourSingletonTrace_secondarySelectorSignedWeight]
    norm_num

theorem ourInvariantSevenAxisCoordinate_ourSingletonTrace
    (policy : PhysicalRelationPolicy) :
    ourInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) = 1 / 2 := by
  unfold ourInvariantSevenAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSingletonTrace,
    derivativeAxisCoordinate_reynolds_ourSingletonTrace]
  norm_num

theorem ourInvariantIBPAxisCoordinate_ourSingletonTrace
    (policy : PhysicalRelationPolicy) :
    ourInvariantIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) = 0 := by
  unfold ourInvariantIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSingletonTrace,
    ourIBPAxisPlanePairCoordinate_reynolds_ourSingletonTrace]
  norm_num

theorem ourInvariantThirdIBPAxisCoordinate_ourSingletonTrace
    (policy : PhysicalRelationPolicy) :
    ourInvariantThirdIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) = 0 := by
  unfold ourInvariantThirdIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSingletonTrace,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourSingletonTrace]
  norm_num

theorem ourInvariantTraceCycleProfileCoordinate_ourSingletonTrace
    (policy : PhysicalRelationPolicy) :
    ourInvariantTraceCycleProfileCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) = -3 / 5 := by
  unfold ourInvariantTraceCycleProfileCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSingletonTrace,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourSingletonTrace]
  norm_num

theorem ourIncomingPlaneProfileInvariantCoordinate_ourSingletonTrace_zero
    (policy : PhysicalRelationPolicy) :
    ourIncomingPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) = 0 := by
  unfold ourIncomingPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSingletonTrace,
    ourDerivativeWordPlanePairCoordinate_reynolds_ourSingletonTrace
      (planeLookup 1 3) (Or.inl rfl)]
  norm_num

theorem ourSecondaryPlaneProfileInvariantCoordinate_ourSingletonTrace_zero
    (policy : PhysicalRelationPolicy) :
    ourSecondaryPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) = 0 := by
  unfold ourSecondaryPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSingletonTrace,
    ourDerivativeWordPlanePairCoordinate_reynolds_ourSingletonTrace
      (planeLookup 0 2) (Or.inr rfl)]
  norm_num

theorem ourCycleProfileInvariantTraceOrderCorrection_ourSingletonTrace
    (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) =
      (-1 / 10 : ℚ) • literalIncomingCommutatorClass := by
  unfold ourCycleProfileInvariantTraceOrderCorrection
    ourTraceCycleProfileInvariantTraceContribution
    ourThreeCoordinateInvariantTraceOrderCorrection
    ourThirdInvariantTraceContribution
    ourTwoCoordinateInvariantTraceOrderCorrection
    ourTwoCoordinateInvariantSevenTraceCompensator
    ourTwoCoordinateInvariantSevenAxisCoordinate
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply]
  rw [ourInvariantSevenAxisCoordinate_ourSingletonTrace,
    ourInvariantIBPAxisCoordinate_ourSingletonTrace,
    ourInvariantThirdIBPAxisCoordinate_ourSingletonTrace,
    exactFieldEightTraceProjection_ourSingletonTrace_zero,
    ourInvariantTraceCycleProfileCoordinate_ourSingletonTrace]
  module

theorem ourThreeClassSourceSevenTraceOrderCorrection_ourSingletonTrace
    (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) =
      (-1 / 10 : ℚ) • literalIncomingCommutatorClass := by
  unfold ourThreeClassSourceSevenTraceOrderCorrection
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smulRight_apply,
    ourCycleProfileInvariantTraceOrderCorrection_ourSingletonTrace,
    ourSecondaryPlaneProfileInvariantCoordinate_ourSingletonTrace_zero,
    ourInvariantThirdIBPAxisCoordinate_ourSingletonTrace, zero_smul,
    sub_zero, add_zero]

theorem ourThreeClassSourceSevenTraceOrderCorrection_ourSingletonTrace_ne_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) ≠ 0 := by
  rw [ourThreeClassSourceSevenTraceOrderCorrection_ourSingletonTrace]
  exact smul_ne_zero (by norm_num) literalIncomingCommutatorClass_ne_zero

/-! ## No repair by the three added selectors with the base held fixed -/

/-- OUR full affine family obtained by adding arbitrary quotient-valued
coefficients to the three currently available source-seven selectors. -/
def ourThreeSelectorSourceSevenExtension
    (incomingValue secondaryValue thirdValue : FieldEightPhysicalTraceQuotient) :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ourCycleProfileInvariantTraceOrderCorrection +
    ourIncomingPlaneProfileInvariantCoordinate.smulRight incomingValue +
      ourSecondaryPlaneProfileInvariantCoordinate.smulRight secondaryValue +
        ourInvariantThirdIBPAxisCoordinate.smulRight thirdValue

/-- Every member of OUR present three-selector affine family has the same
nonzero singleton-trace value: all three selectors vanish there. -/
theorem ourThreeSelectorSourceSevenExtension_ourSingletonTrace
    (policy : PhysicalRelationPolicy)
    (incomingValue secondaryValue thirdValue : FieldEightPhysicalTraceQuotient) :
    ourThreeSelectorSourceSevenExtension incomingValue secondaryValue thirdValue
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) =
      (-1 / 10 : ℚ) • literalIncomingCommutatorClass := by
  unfold ourThreeSelectorSourceSevenExtension
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourCycleProfileInvariantTraceOrderCorrection_ourSingletonTrace,
    ourIncomingPlaneProfileInvariantCoordinate_ourSingletonTrace_zero,
    ourSecondaryPlaneProfileInvariantCoordinate_ourSingletonTrace_zero,
    ourInvariantThirdIBPAxisCoordinate_ourSingletonTrace, zero_smul]
  abel

/-- No choice of the three added selector values, with the cycle-profile base
held fixed, can descend through the full physical relation submodule: the
actual singleton-trace row remains outside its kernel. -/
theorem ourThreeSelectorSourceSevenExtension_not_descends
    (policy : PhysicalRelationPolicy)
    (incomingValue secondaryValue thirdValue : FieldEightPhysicalTraceQuotient) :
    ¬ orbitPhysicalRelationSubmodule policy ≤
      LinearMap.ker
        (ourThreeSelectorSourceSevenExtension
          incomingValue secondaryValue thirdValue) := by
  intro hdescent
  have hmember :
      orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1) ∈
        orbitPhysicalRelationSubmodule policy :=
    ⟨Finsupp.single (ourSingletonTraceGenerator policy) 1, rfl⟩
  have hzero := LinearMap.mem_ker.mp (hdescent hmember)
  rw [ourThreeSelectorSourceSevenExtension_ourSingletonTrace] at hzero
  exact smul_ne_zero (by norm_num) literalIncomingCommutatorClass_ne_zero hzero

theorem ourSingletonTrace_sourceFieldCount :
    physicalRelationGeneratorSourceFieldCount
      (ourSingletonTraceGenerator .offShell) = ourSevenFieldCount := by
  rfl

#print axioms ourSingletonTrace_signedAxisWeight
#print axioms orbitPhysicalRelationOperator_ourSingletonTrace
#print axioms ourThreeClassSourceSevenTraceOrderCorrection_ourSingletonTrace
#print axioms ourThreeClassSourceSevenTraceOrderCorrection_ourSingletonTrace_ne_zero
#print axioms ourThreeSelectorSourceSevenExtension_not_descends

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation
