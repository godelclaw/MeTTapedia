import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderSecondaryAxisData
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderSecondaryIBPData
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderSecondaryProfileData
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingIBPData
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingSecondIBPDataBlock00
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingSecondIBPDataBlock01
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingSecondIBPDataBlock02
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingSecondIBPDataBlock03
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingBianchiDataBlock00
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingBianchiDataBlock01
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingEOMDataBlock00
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingEOMDataBlock01
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingFundamentalData
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingTraceAnticommutatorData

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
open HypercubicDimension16WilsonTraceOrderInvariantBianchi
open HypercubicDimension16WilsonTraceOrderInvariantEOM
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileDifferential
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassCompatibility
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch
open HypercubicDimension16WilsonTraceOrderSecondaryAxisData
open HypercubicDimension16WilsonTraceOrderSecondaryIBPData
open HypercubicDimension16WilsonTraceOrderSecondaryProfileData
open HypercubicDimension16WilsonTraceOrderIncomingIBPData
open HypercubicDimension16WilsonTraceOrderIncomingSecondIBPDataBlock00
open HypercubicDimension16WilsonTraceOrderIncomingSecondIBPDataBlock01
open HypercubicDimension16WilsonTraceOrderIncomingSecondIBPDataBlock02
open HypercubicDimension16WilsonTraceOrderIncomingSecondIBPDataBlock03
open HypercubicDimension16WilsonTraceOrderIncomingBianchiDataBlock00
open HypercubicDimension16WilsonTraceOrderIncomingBianchiDataBlock01
open HypercubicDimension16WilsonTraceOrderIncomingEOMDataBlock00
open HypercubicDimension16WilsonTraceOrderIncomingEOMDataBlock01
open HypercubicDimension16WilsonTraceOrderIncomingFundamentalData
open HypercubicDimension16WilsonTraceOrderIncomingTraceAnticommutatorData
open HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair
open HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction

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

/-! ## First-IBP replay -/

set_option maxRecDepth 100000 in
theorem ourIncomingPlaneProfileCoordinate_reynolds_ourIBP
    (field : Fin 7) :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (ourIBPOrbit field) (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ (ourIBPLabeledTerm field) : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) (ourIBPLabeledTerm field) 0
    (ourIBP_incomingPlaneProfileSignedWeight field)]
  norm_num

theorem ourIncomingPlaneProfileCoordinate_reynolds_ourIBPRow :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (∑ field : Fin 7, Finsupp.single (ourIBPOrbit field) (1 : ℚ))) = 0 := by
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro field _
  exact ourIncomingPlaneProfileCoordinate_reynolds_ourIBP field

theorem ourIncomingPlaneProfileInvariantCoordinate_ourIBP_zero :
    ourIncomingPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 := by
  unfold ourIncomingPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourIBP,
    ourIncomingPlaneProfileCoordinate_reynolds_ourIBPRow]
  norm_num

theorem ourExistingScalarNullDirection_ourIBP_zero :
    ourExistingScalarNullDirection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 := by
  unfold ourExistingScalarNullDirection
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.smul_apply]
  rw [ourInvariantSevenAxisCoordinate_ourIBP,
    ourInvariantIBPAxisCoordinate_ourIBP,
    ourInvariantThirdIBPAxisCoordinate_ourIBP,
    ourInvariantTraceCycleProfileCoordinate_ourIBP_zero,
    ourIncomingPlaneProfileInvariantCoordinate_ourIBP_zero,
    ourSecondaryPlaneProfileInvariantCoordinate_ourIBP_zero]
  norm_num

/-! ## Second-IBP replay -/

theorem ourSecondIBP_incomingPlaneProfileSignedWeight
    (field : Fin 7) :
    (∑ h : Hypercubic4,
      (ourSecondIBPLabeledTerm field).tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3)
          ((ourSecondIBPLabeledTerm field).hypercubicAct h) : ℚ)) = 0 := by
  fin_cases field
  · exact ourSecondIBP_incomingPlaneProfileSignedWeight_zero
  · exact ourSecondIBP_incomingPlaneProfileSignedWeight_one
  · exact ourSecondIBP_incomingPlaneProfileSignedWeight_two
  · exact ourSecondIBP_incomingPlaneProfileSignedWeight_three
  · exact ourSecondIBP_incomingPlaneProfileSignedWeight_four
  · exact ourSecondIBP_incomingPlaneProfileSignedWeight_five
  · exact ourSecondIBP_incomingPlaneProfileSignedWeight_six

set_option maxRecDepth 100000 in
theorem ourIncomingPlaneProfileCoordinate_reynolds_ourSecondIBP
    (field : Fin 7) :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (ourSecondIBPOrbit field) (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ (ourSecondIBPLabeledTerm field) : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) (ourSecondIBPLabeledTerm field) 0
    (ourSecondIBP_incomingPlaneProfileSignedWeight field)]
  norm_num

theorem ourIncomingPlaneProfileCoordinate_reynolds_ourSecondIBPRow :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (∑ field : Fin 7, Finsupp.single (ourSecondIBPOrbit field) (1 : ℚ))) =
        0 := by
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro field _
  exact ourIncomingPlaneProfileCoordinate_reynolds_ourSecondIBP field

theorem ourIncomingPlaneProfileInvariantCoordinate_ourSecondIBP_zero
    (policy : PhysicalRelationPolicy) :
    ourIncomingPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 := by
  unfold ourIncomingPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSecondIBP,
    ourIncomingPlaneProfileCoordinate_reynolds_ourSecondIBPRow]
  norm_num

theorem ourExistingScalarNullDirection_ourSecondIBP_zero
    (policy : PhysicalRelationPolicy) :
    ourExistingScalarNullDirection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 := by
  unfold ourExistingScalarNullDirection
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.smul_apply]
  rw [ourInvariantSevenAxisCoordinate_ourSecondIBP,
    ourInvariantIBPAxisCoordinate_ourSecondIBP,
    ourInvariantThirdIBPAxisCoordinate_ourSecondIBP,
    ourInvariantTraceCycleProfileCoordinate_ourSecondIBP_zero,
    ourIncomingPlaneProfileInvariantCoordinate_ourSecondIBP_zero,
    ourSecondaryPlaneProfileInvariantCoordinate_ourSecondIBP]
  norm_num

/-! ## Bianchi replay -/

set_option maxRecDepth 100000 in
theorem ourIncomingPlaneProfileCoordinate_reynolds_ourBianchiBase :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiBaseOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourBianchiBaseLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) ourBianchiBaseLabeled 0
    ourBianchiBase_incomingPlaneProfileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourIncomingPlaneProfileCoordinate_reynolds_ourBianchiRotateOne :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateOneOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourBianchiRotateOneLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) ourBianchiRotateOneLabeled 0
    ourBianchiRotateOne_incomingPlaneProfileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourIncomingPlaneProfileCoordinate_reynolds_ourBianchiRotateTwo :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateTwoOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourBianchiRotateTwoLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) ourBianchiRotateTwoLabeled 0
    ourBianchiRotateTwo_incomingPlaneProfileSignedWeight]
  norm_num

theorem ourIncomingPlaneProfileCoordinate_reynolds_ourBianchiRotateOne_neg :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateOneOrbit (-1 : ℚ))) = 0 := by
  rw [show Finsupp.single ourBianchiRotateOneOrbit (-1 : ℚ) =
      -Finsupp.single ourBianchiRotateOneOrbit (1 : ℚ) by simp,
    map_neg, map_neg, ourIncomingPlaneProfileCoordinate_reynolds_ourBianchiRotateOne]
  simp

theorem ourIncomingPlaneProfileInvariantCoordinate_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourIncomingPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  unfold ourIncomingPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourBianchi]
  simp only [LinearMap.map_add,
    ourIncomingPlaneProfileCoordinate_reynolds_ourBianchiBase,
    ourIncomingPlaneProfileCoordinate_reynolds_ourBianchiRotateOne_neg,
    ourIncomingPlaneProfileCoordinate_reynolds_ourBianchiRotateTwo]
  norm_num

theorem ourExistingScalarNullDirection_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourExistingScalarNullDirection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  unfold ourExistingScalarNullDirection
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.smul_apply]
  rw [ourInvariantSevenAxisCoordinate_ourBianchi_zero,
    ourInvariantIBPAxisCoordinate_ourBianchi_zero,
    ourInvariantThirdIBPAxisCoordinate_ourBianchi_zero,
    ourInvariantTraceCycleProfileCoordinate_ourBianchi_zero,
    ourIncomingPlaneProfileInvariantCoordinate_ourBianchi_zero,
    ourSecondaryPlaneProfileInvariantCoordinate_ourBianchi_zero]
  norm_num

/-! ## On-shell EOM replay -/

set_option maxRecDepth 100000 in
theorem ourIncomingPlaneProfileCoordinate_reynolds_ourEOMZero :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMZeroOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourEOMZeroLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) ourEOMZeroLabeled 0
    ourEOMZero_incomingPlaneProfileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourIncomingPlaneProfileCoordinate_reynolds_ourEOMOne :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMOneOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourEOMOneLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) ourEOMOneLabeled 0
    ourEOMOne_incomingPlaneProfileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourIncomingPlaneProfileCoordinate_reynolds_ourEOMThree :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMThreeOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourEOMThreeLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) ourEOMThreeLabeled 0
    ourEOMThree_incomingPlaneProfileSignedWeight]
  norm_num

theorem ourIncomingPlaneProfileCoordinate_reynolds_ourEOMThree_neg :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMThreeOrbit (-1 : ℚ))) = 0 := by
  rw [show Finsupp.single ourEOMThreeOrbit (-1 : ℚ) =
      -Finsupp.single ourEOMThreeOrbit (1 : ℚ) by simp,
    map_neg, map_neg, ourIncomingPlaneProfileCoordinate_reynolds_ourEOMThree]
  simp

theorem ourIncomingPlaneProfileInvariantCoordinate_ourEOM_zero :
    ourIncomingPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  unfold ourIncomingPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourEOM]
  simp only [LinearMap.map_add,
    ourIncomingPlaneProfileCoordinate_reynolds_ourEOMZero,
    ourIncomingPlaneProfileCoordinate_reynolds_ourEOMOne,
    ourIncomingPlaneProfileCoordinate_reynolds_ourEOMThree_neg]
  norm_num

theorem ourExistingScalarNullDirection_ourEOM_zero :
    ourExistingScalarNullDirection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  unfold ourExistingScalarNullDirection
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.smul_apply]
  rw [ourInvariantSevenAxisCoordinate_ourEOM_zero,
    ourInvariantIBPAxisCoordinate_ourEOM_zero,
    ourInvariantThirdIBPAxisCoordinate_ourEOM_zero,
    ourInvariantTraceCycleProfileCoordinate_ourEOM_zero,
    ourIncomingPlaneProfileInvariantCoordinate_ourEOM_zero,
    ourSecondaryPlaneProfileInvariantCoordinate_ourEOM_zero]
  norm_num

/-! ## Fundamental three-cut replay -/

set_option maxRecDepth 100000 in
theorem ourIncomingPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutBase :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutBaseOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutBaseLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) ourFundamentalThreeCutBaseLabeled 0
    ourFundamentalThreeCutBase_incomingPlaneProfileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourIncomingPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutSwapFirstSecond :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutSwapFirstSecondOrbit (1 : ℚ))) =
      0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutSwapFirstSecondLabeled :
            FieldSevenOrbitCarrier) (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) ourFundamentalThreeCutSwapFirstSecondLabeled 0
    ourFundamentalThreeCutSwapFirstSecond_incomingPlaneProfileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourIncomingPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutSwapFirstThird :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutSwapFirstThirdOrbit (1 : ℚ))) =
      0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutSwapFirstThirdLabeled :
            FieldSevenOrbitCarrier) (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) ourFundamentalThreeCutSwapFirstThirdLabeled 0
    ourFundamentalThreeCutSwapFirstThird_incomingPlaneProfileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourIncomingPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutSwapSecondThird :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutSwapSecondThirdOrbit (1 : ℚ))) =
      0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutSwapSecondThirdLabeled :
            FieldSevenOrbitCarrier) (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) ourFundamentalThreeCutSwapSecondThirdLabeled 0
    ourFundamentalThreeCutSwapSecondThird_incomingPlaneProfileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourIncomingPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutForward :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutForwardOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutForwardLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) ourFundamentalThreeCutForwardLabeled 0
    ourFundamentalThreeCutForward_incomingPlaneProfileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourIncomingPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutBackward :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutBackwardOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutBackwardLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) ourFundamentalThreeCutBackwardLabeled 0
    ourFundamentalThreeCutBackward_incomingPlaneProfileSignedWeight]
  norm_num

theorem ourIncomingPlaneProfileCoordinate_reynolds_ourFundamentalThreeCut :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutBaseOrbit 1 -
          Finsupp.single ourFundamentalThreeCutSwapFirstSecondOrbit 1 -
            Finsupp.single ourFundamentalThreeCutSwapFirstThirdOrbit 1 -
              Finsupp.single ourFundamentalThreeCutSwapSecondThirdOrbit 1 +
                Finsupp.single ourFundamentalThreeCutForwardOrbit 1 +
                  Finsupp.single ourFundamentalThreeCutBackwardOrbit 1)) = 0 := by
  simp only [LinearMap.map_sub, LinearMap.map_add,
    ourIncomingPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutBase,
    ourIncomingPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutSwapFirstSecond,
    ourIncomingPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutSwapFirstThird,
    ourIncomingPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutSwapSecondThird,
    ourIncomingPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutForward,
    ourIncomingPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutBackward]
  norm_num

theorem ourIncomingPlaneProfileInvariantCoordinate_ourFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourIncomingPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 := by
  unfold ourIncomingPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourFundamentalThreeCut,
    ourIncomingPlaneProfileCoordinate_reynolds_ourFundamentalThreeCut]
  norm_num

theorem ourExistingScalarNullDirection_ourFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourExistingScalarNullDirection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 := by
  unfold ourExistingScalarNullDirection
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.smul_apply]
  rw [ourInvariantSevenAxisCoordinate_ourFundamentalThreeCut_zero,
    ourInvariantIBPAxisCoordinate_ourFundamentalThreeCut_zero,
    ourInvariantThirdIBPAxisCoordinate_ourFundamentalThreeCut_zero,
    ourInvariantTraceCycleProfileCoordinate_ourFundamentalThreeCut_zero,
    ourIncomingPlaneProfileInvariantCoordinate_ourFundamentalThreeCut_zero,
    ourSecondaryPlaneProfileInvariantCoordinate_ourFundamentalThreeCut_zero]
  norm_num

/-! ## Polarized trace-anticommutator replay -/

set_option maxRecDepth 100000 in
theorem ourIncomingPlaneProfileCoordinate_reynolds_ourTraceAnticommutatorBase :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorBaseOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourTraceAnticommutatorBaseLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) ourTraceAnticommutatorBaseLabeled 0
    ourTraceAnticommutatorBase_incomingPlaneProfileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourIncomingPlaneProfileCoordinate_reynolds_ourTraceAnticommutatorSwap :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorSwapOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourTraceAnticommutatorSwapLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) ourTraceAnticommutatorSwapLabeled 0
    ourTraceAnticommutatorSwap_incomingPlaneProfileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourIncomingPlaneProfileCoordinate_reynolds_ourTraceAnticommutatorSplit :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorSplitOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourTraceAnticommutatorSplitLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) ourTraceAnticommutatorSplitLabeled 0
    ourTraceAnticommutatorSplit_incomingPlaneProfileSignedWeight]
  norm_num

theorem ourIncomingPlaneProfileCoordinate_reynolds_ourTraceAnticommutator :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorBaseOrbit 1 +
          Finsupp.single ourTraceAnticommutatorSwapOrbit 1 -
            Finsupp.single ourTraceAnticommutatorSplitOrbit 1)) = 0 := by
  simp only [LinearMap.map_sub, LinearMap.map_add,
    ourIncomingPlaneProfileCoordinate_reynolds_ourTraceAnticommutatorBase,
    ourIncomingPlaneProfileCoordinate_reynolds_ourTraceAnticommutatorSwap,
    ourIncomingPlaneProfileCoordinate_reynolds_ourTraceAnticommutatorSplit]
  norm_num

theorem ourIncomingPlaneProfileInvariantCoordinate_ourTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourIncomingPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 := by
  unfold ourIncomingPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourTraceAnticommutator,
    ourIncomingPlaneProfileCoordinate_reynolds_ourTraceAnticommutator]
  norm_num

theorem ourExistingScalarNullDirection_ourTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourExistingScalarNullDirection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 := by
  unfold ourExistingScalarNullDirection
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.smul_apply]
  rw [ourInvariantSevenAxisCoordinate_ourTraceAnticommutator,
    ourInvariantIBPAxisCoordinate_ourTraceAnticommutator_zero,
    ourInvariantThirdIBPAxisCoordinate_ourTraceAnticommutator_zero,
    ourInvariantTraceCycleProfileCoordinate_ourTraceAnticommutator,
    ourIncomingPlaneProfileInvariantCoordinate_ourTraceAnticommutator_zero,
    ourSecondaryPlaneProfileInvariantCoordinate_ourTraceAnticommutator_zero]
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

/-- OUR reparameterized correction retains the explicitly checked first-IBP
row under the off-shell physical policy. -/
theorem ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourIBP_zero :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 := by
  unfold ourParameterSynthesizedSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourThreeClassSourceSevenTraceOrderCorrection_ourIBP_zero,
    ourExistingScalarNullDirection_ourIBP_zero, zero_smul]
  simp

/-- OUR reparameterized correction retains the explicitly checked second-IBP
row under either physical relation policy. -/
theorem ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSecondIBP_zero
    (policy : PhysicalRelationPolicy) :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 := by
  unfold ourParameterSynthesizedSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourThreeClassSourceSevenTraceOrderCorrection_ourSecondIBP_zero,
    ourExistingScalarNullDirection_ourSecondIBP_zero, zero_smul]
  simp

/-- OUR reparameterized correction retains the explicitly checked Bianchi row
under either physical relation policy. -/
theorem ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  unfold ourParameterSynthesizedSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourThreeClassSourceSevenTraceOrderCorrection_ourBianchi_zero,
    ourExistingScalarNullDirection_ourBianchi_zero, zero_smul]
  simp

/-- OUR reparameterized correction retains the explicitly checked on-shell
EOM row. -/
theorem ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourEOM_zero :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  unfold ourParameterSynthesizedSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourThreeClassSourceSevenTraceOrderCorrection_ourEOM_zero,
    ourExistingScalarNullDirection_ourEOM_zero, zero_smul]
  simp

/-- OUR reparameterized correction retains the explicitly checked fundamental
three-cut trace row under either physical relation policy. -/
theorem ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 := by
  unfold ourParameterSynthesizedSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourThreeClassSourceSevenTraceOrderCorrection_ourFundamentalThreeCut_zero,
    ourExistingScalarNullDirection_ourFundamentalThreeCut_zero, zero_smul]
  simp

/-- OUR reparameterized correction retains the explicitly checked polarized
trace-anticommutator row under either physical relation policy. -/
theorem ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 := by
  unfold ourParameterSynthesizedSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourThreeClassSourceSevenTraceOrderCorrection_ourTraceAnticommutator_zero,
    ourExistingScalarNullDirection_ourTraceAnticommutator_zero, zero_smul]
  simp

#print axioms ourExistingScalarNullDirection_ourSingletonTrace
#print axioms ourExistingScalarNullDirection_ourCommutator_zero
#print axioms ourExistingScalarNullDirection_ourSecondaryCommutator_zero
#print axioms ourExistingScalarNullDirection_ourIBP_zero
#print axioms ourExistingScalarNullDirection_ourSecondIBP_zero
#print axioms ourExistingScalarNullDirection_ourBianchi_zero
#print axioms ourExistingScalarNullDirection_ourEOM_zero
#print axioms ourExistingScalarNullDirection_ourFundamentalThreeCut_zero
#print axioms ourExistingScalarNullDirection_ourTraceAnticommutator_zero
#print axioms ourExistingScalarNullDirection_signed_action
#print axioms ourParameterSynthesizedSourceSevenTraceOrderCorrection_signed_action
#print axioms ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSingletonTrace_zero
#print axioms ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourCommutator_zero
#print axioms ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero
#print axioms ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourIBP_zero
#print axioms ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSecondIBP_zero
#print axioms ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourBianchi_zero
#print axioms ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourEOM_zero
#print axioms ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourFundamentalThreeCut_zero
#print axioms ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourTraceAnticommutator_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepair
