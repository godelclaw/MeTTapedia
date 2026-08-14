import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderSecondaryAxisData
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderSecondaryIBPData
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderSecondaryProfileData

/-!
# OUR existing-scalar parameter repair of the singleton trace row

The fixed-base three-selector extension fails on the actual singleton-trace
relation.  That negative result left a specific finite question: whether the
six scalar coordinates already present in OUR construction have a deformation
which retains the previously checked rows and cancels that mismatch.

This module constructs the candidate deformation and first checks its exact
singleton value.  It is a finite named-row repair only.  It does not assert
descent through the complete physical relation submodule, a complete
source-seven census, joint rank or conditioning, nor Wilson-functional
coordinates.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepair

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16CovariantCommutator
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
open HypercubicDimension16IncomingCommutatorTraceCoupledColumn
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16FieldEightTracePhysicalLift
open SU2LatticeFDCensusNoGo
open V14HypercubicQuarticCensus
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileDifferential
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch
open HypercubicDimension16WilsonTraceOrderSecondaryAxisData
open HypercubicDimension16WilsonTraceOrderSecondaryIBPData
open HypercubicDimension16WilsonTraceOrderSecondaryProfileData

/-- OUR scalar null-direction candidate over the six already constructed
coordinates.  Its signs are chosen so that a unit evaluation on the original
seven-axis coordinate corresponds to the unique homogeneous deformation
tested below. -/
def ourExistingScalarNullDirection :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] ℚ :=
  -ourInvariantSevenAxisCoordinate +
    (1 / 2 : ℚ) • ourInvariantIBPAxisCoordinate -
      (1 / 2 : ℚ) • ourInvariantThirdIBPAxisCoordinate -
        ourInvariantTraceCycleProfileCoordinate +
          ourIncomingPlaneProfileInvariantCoordinate +
            ourSecondaryPlaneProfileInvariantCoordinate

/-- The scalar deformation is signed-`H(4)`-invariant, so it stays within
the same coordinate-free invariant interface as the preceding correction. -/
theorem ourExistingScalarNullDirection_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourExistingScalarNullDirection (signedExactFieldRelabelOrbitAction h value) =
      ourExistingScalarNullDirection value := by
  unfold ourExistingScalarNullDirection
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.smul_apply]
  rw [ourInvariantSevenAxisCoordinate_signed_action,
    ourInvariantIBPAxisCoordinate_signed_action,
    ourInvariantThirdIBPAxisCoordinate_signed_action,
    ourInvariantTraceCycleProfileCoordinate_signed_action,
    ourIncomingPlaneProfileInvariantCoordinate_signed_action,
    ourSecondaryPlaneProfileInvariantCoordinate_signed_action]

/-- OUR reparameterized source-seven correction: the previously refuted
fixed-base map plus the scalar null direction applied to the already
certified nonzero incoming trace class. -/
def ourParameterSynthesizedSourceSevenTraceOrderCorrection :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ourThreeClassSourceSevenTraceOrderCorrection +
    ourExistingScalarNullDirection.smulRight literalIncomingCommutatorClass

/-- The reparameterized correction remains signed-`H(4)`-invariant. -/
theorem ourParameterSynthesizedSourceSevenTraceOrderCorrection_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (signedExactFieldRelabelOrbitAction h value) =
      ourParameterSynthesizedSourceSevenTraceOrderCorrection value := by
  unfold ourParameterSynthesizedSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply]
  rw [ourThreeClassSourceSevenTraceOrderCorrection_signed_action,
    ourExistingScalarNullDirection_signed_action]

/-! ## Secondary commutator replay -/

theorem derivativeAxisOrbitMultiplicity_ourSecondarySource_action
    (h : Hypercubic4) :
    derivativeAxisOrbitMultiplicity [0, 2]
      (ourSecondarySourceSevenOrbit.hypercubicAct h) =
        (derivativeAxisWordMultiplicity [0, 2]
          (ourSecondarySourceLabeled.hypercubicAct h) : ℚ) := by
  simp [derivativeAxisOrbitMultiplicity, ourSecondarySourceSevenOrbit]

theorem derivativeAxisOrbitMultiplicity_ourSecondarySwapped_action
    (h : Hypercubic4) :
    derivativeAxisOrbitMultiplicity [0, 2]
      (ourSecondarySwappedSevenOrbit.hypercubicAct h) =
        (derivativeAxisWordMultiplicity [0, 2]
          (ourSecondarySwappedLabeled.hypercubicAct h) : ℚ) := by
  simp [derivativeAxisOrbitMultiplicity, ourSecondarySwappedSevenOrbit]

theorem derivativeAxisCoordinate_reynolds_ourSecondarySource :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSecondarySourceSevenOrbit (1 : ℚ))) = 1 / 12 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourSecondarySourceSevenOrbit (1 : ℚ))) =
        ourSecondarySourceLabeled.tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            (ourSecondarySourceLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single,
      derivativeAxisOrbitMultiplicity_ourSecondarySource_action]
    simp [ourSecondarySourceSevenOrbit]
  simp_rw [hterm]
  rw [ourSecondarySource_signedAxisWeight]
  norm_num

theorem derivativeAxisCoordinate_reynolds_ourSecondarySwapped :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSecondarySwappedSevenOrbit (1 : ℚ))) = -(1 / 12) := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourSecondarySwappedSevenOrbit (1 : ℚ))) =
        ourSecondarySwappedLabeled.tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            (ourSecondarySwappedLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single,
      derivativeAxisOrbitMultiplicity_ourSecondarySwapped_action]
    simp [ourSecondarySwappedSevenOrbit]
  simp_rw [hterm]
  rw [ourSecondarySwapped_signedAxisWeight]
  norm_num

theorem derivativeAxisCoordinate_reynolds_secondary_fst :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2 ourSecondaryCoupledCommutatorVector.1) =
        1 / 6 := by
  rw [ourSecondaryCoupledCommutatorVector_fst, LinearMap.map_sub,
    LinearMap.map_sub, derivativeAxisCoordinate_reynolds_ourSecondarySource,
    derivativeAxisCoordinate_reynolds_ourSecondarySwapped]
  norm_num

theorem ourInvariantSevenAxisCoordinate_ourSecondaryCommutator
    (policy : PhysicalRelationPolicy) :
    ourInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
        1 := by
  unfold ourInvariantSevenAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSecondaryCommutator_full,
    derivativeAxisCoordinate_reynolds_secondary_fst]
  norm_num

theorem ourIBPAxisPlanePairOrbitMultiplicity_ourSecondarySource_action
    (h : Hypercubic4) :
    ourIBPAxisPlanePairOrbitMultiplicity
      (ourSecondarySourceSevenOrbit.hypercubicAct h) =
        (ourIBPAxisPlanePairMultiplicity
          (ourSecondarySourceLabeled.hypercubicAct h) : ℚ) := by
  simp [ourIBPAxisPlanePairOrbitMultiplicity, ourSecondarySourceSevenOrbit]

theorem ourIBPAxisPlanePairOrbitMultiplicity_ourSecondarySwapped_action
    (h : Hypercubic4) :
    ourIBPAxisPlanePairOrbitMultiplicity
      (ourSecondarySwappedSevenOrbit.hypercubicAct h) =
        (ourIBPAxisPlanePairMultiplicity
          (ourSecondarySwappedLabeled.hypercubicAct h) : ℚ) := by
  simp [ourIBPAxisPlanePairOrbitMultiplicity, ourSecondarySwappedSevenOrbit]

theorem ourIBPAxisPlanePairCoordinate_reynolds_ourSecondarySource :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSecondarySourceSevenOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourSecondarySourceSevenOrbit (1 : ℚ))) =
        ourSecondarySourceLabeled.tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            (ourSecondarySourceLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single,
      ourIBPAxisPlanePairOrbitMultiplicity_ourSecondarySource_action]
    simp [ourSecondarySourceSevenOrbit]
  simp_rw [hterm]
  rw [ourSecondarySource_IBPAxisPlanePairSignedWeight]
  norm_num

theorem ourIBPAxisPlanePairCoordinate_reynolds_ourSecondarySwapped :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSecondarySwappedSevenOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourSecondarySwappedSevenOrbit (1 : ℚ))) =
        ourSecondarySwappedLabeled.tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            (ourSecondarySwappedLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single,
      ourIBPAxisPlanePairOrbitMultiplicity_ourSecondarySwapped_action]
    simp [ourSecondarySwappedSevenOrbit]
  simp_rw [hterm]
  rw [ourSecondarySwapped_IBPAxisPlanePairSignedWeight]
  norm_num

theorem ourIBPAxisPlanePairCoordinate_reynolds_secondary_fst :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2 ourSecondaryCoupledCommutatorVector.1) = 0 := by
  rw [ourSecondaryCoupledCommutatorVector_fst, LinearMap.map_sub,
    LinearMap.map_sub, ourIBPAxisPlanePairCoordinate_reynolds_ourSecondarySource,
    ourIBPAxisPlanePairCoordinate_reynolds_ourSecondarySwapped]
  norm_num

theorem ourInvariantIBPAxisCoordinate_ourSecondaryCommutator
    (policy : PhysicalRelationPolicy) :
    ourInvariantIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
        0 := by
  unfold ourInvariantIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSecondaryCommutator_full,
    ourIBPAxisPlanePairCoordinate_reynolds_secondary_fst]
  norm_num

set_option maxRecDepth 100000 in
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourSecondarySource :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSecondarySourceSevenOrbit (1 : ℚ))) = 0 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourSecondarySourceLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourSecondarySourceLabeled 0 ourSecondarySource_profileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourSecondarySwapped :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSecondarySwappedSevenOrbit (1 : ℚ))) = 0 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourSecondarySwappedLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourSecondarySwappedLabeled 0 ourSecondarySwapped_profileSignedWeight]
  norm_num

theorem ourTraceCycleProfileAxisCoordinate_reynolds_secondary_fst :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2 ourSecondaryCoupledCommutatorVector.1) = 0 := by
  rw [ourSecondaryCoupledCommutatorVector_fst, LinearMap.map_sub,
    LinearMap.map_sub,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourSecondarySource,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourSecondarySwapped]
  norm_num

theorem ourInvariantTraceCycleProfileCoordinate_ourSecondaryCommutator
    (policy : PhysicalRelationPolicy) :
    ourInvariantTraceCycleProfileCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
        0 := by
  unfold ourInvariantTraceCycleProfileCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSecondaryCommutator_full,
    ourTraceCycleProfileAxisCoordinate_reynolds_secondary_fst]
  norm_num

/-- The existing scalar deformation also vanishes on the independent
secondary source-seven commutator. -/
theorem ourExistingScalarNullDirection_ourSecondaryCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourExistingScalarNullDirection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
        0 := by
  unfold ourExistingScalarNullDirection
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.smul_apply]
  rw [ourInvariantSevenAxisCoordinate_ourSecondaryCommutator,
    ourInvariantIBPAxisCoordinate_ourSecondaryCommutator,
    ourInvariantThirdIBPAxisCoordinate_ourSecondaryCommutator,
    ourInvariantTraceCycleProfileCoordinate_ourSecondaryCommutator,
    ourIncomingPlaneProfileInvariantCoordinate_ourSecondaryCommutator,
    ourSecondaryPlaneProfileInvariantCoordinate_ourSecondaryCommutator]
  norm_num

/-- The existing scalar null direction contributes exactly `1 / 10` of the
incoming trace class on the singleton-trace row. -/
theorem ourExistingScalarNullDirection_ourSingletonTrace
    (policy : PhysicalRelationPolicy) :
    ourExistingScalarNullDirection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) = 1 / 10 := by
  unfold ourExistingScalarNullDirection
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.smul_apply]
  rw [ourInvariantSevenAxisCoordinate_ourSingletonTrace,
    ourInvariantIBPAxisCoordinate_ourSingletonTrace,
    ourInvariantThirdIBPAxisCoordinate_ourSingletonTrace,
    ourInvariantTraceCycleProfileCoordinate_ourSingletonTrace,
    ourIncomingPlaneProfileInvariantCoordinate_ourSingletonTrace_zero,
    ourSecondaryPlaneProfileInvariantCoordinate_ourSingletonTrace_zero]
  norm_num

/-- The scalar deformation vanishes on the original concrete source-seven
commutator.  Thus the singleton repair retains this previously checked row. -/
theorem ourExistingScalarNullDirection_ourCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourExistingScalarNullDirection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  unfold ourExistingScalarNullDirection
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.smul_apply]
  rw [ourInvariantSevenAxisCoordinate_ourCommutator,
    ourInvariantIBPAxisCoordinate_ourCommutator,
    ourInvariantThirdIBPAxisCoordinate_ourCommutator,
    ourInvariantTraceCycleProfileCoordinate_ourCommutator_zero,
    ourIncomingPlaneProfileInvariantCoordinate_ourCommutator,
    ourSecondaryPlaneProfileInvariantCoordinate_ourCommutator]
  norm_num

/-- OUR reparameterized correction annihilates the explicit singleton-trace
relation under either physical policy. -/
theorem ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSingletonTrace_zero
    (policy : PhysicalRelationPolicy) :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) = 0 := by
  unfold ourParameterSynthesizedSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourThreeClassSourceSevenTraceOrderCorrection_ourSingletonTrace,
    ourExistingScalarNullDirection_ourSingletonTrace]
  module

/-- OUR reparameterized correction retains the original explicit incoming
source-seven commutator under either physical policy. -/
theorem ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  unfold ourParameterSynthesizedSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourThreeClassSourceSevenTraceOrderCorrection_ourCommutator_zero,
    ourExistingScalarNullDirection_ourCommutator_zero, zero_smul]
  simp

/-- OUR reparameterized correction retains the independent secondary
source-seven commutator under either physical policy. -/
theorem ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
        0 := by
  unfold ourParameterSynthesizedSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourThreeClassSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero,
    ourExistingScalarNullDirection_ourSecondaryCommutator_zero, zero_smul]
  simp

#print axioms ourExistingScalarNullDirection_ourSingletonTrace
#print axioms ourExistingScalarNullDirection_ourCommutator_zero
#print axioms ourExistingScalarNullDirection_ourSecondaryCommutator_zero
#print axioms ourExistingScalarNullDirection_signed_action
#print axioms ourParameterSynthesizedSourceSevenTraceOrderCorrection_signed_action
#print axioms ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSingletonTrace_zero
#print axioms ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourCommutator_zero
#print axioms ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepair
