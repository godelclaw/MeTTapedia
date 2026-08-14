import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassCompatibility

/-!
# OUR three-class source-seven repair

The secondary plane-profile selector repairs the second concrete source-seven
commutator, but the compatibility audit finds its normalized value is one on
the genuine second-IBP row.  This module reuses the independent third
split-derivative/plane coordinate already calibrated on that row.  Its finite
signed-`H(4)` sums vanish on both source-seven commutators, while its normalized
second-IBP value is one.  Adding it with the same exact residual therefore
cancels the two-class mismatch without disturbing either commutator.

This is an OUR finite repair of the listed physical rows.  It does not assert
descent through the complete source-seven relation submodule, a joint-rank
calculation, conditioning, or Wilson-functional coordinates.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepair

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open SU2LatticeFDCensusNoGo
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16AntisymmetryQuotient
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16IncomingCommutatorTraceCoupledColumn
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceProjection
open HypercubicDimension16IncomingCommutatorTraceInvariantWitness
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16FieldEightTracePhysicalLift
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderInvariantBianchi
open HypercubicDimension16WilsonTraceOrderInvariantEOM
open HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair
open HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileDifferential
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenCorrectionRefutation
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassCompatibility

/-! ## Secondary source-seven calibration of the third coordinate -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced third-coordinate numerator of the secondary source. -/
theorem ourSecondarySource_thirdIBPAxisPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourSecondarySourceLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourSecondarySourceLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced third-coordinate numerator of the swapped secondary
source. -/
theorem ourSecondarySwapped_thirdIBPAxisPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourSecondarySwappedLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourSecondarySwappedLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

theorem ourThirdIBPAxisPlanePairOrbitMultiplicity_ourSecondarySource_action
    (h : Hypercubic4) :
    ourThirdIBPAxisPlanePairOrbitMultiplicity
      (ourSecondarySourceSevenOrbit.hypercubicAct h) =
      (ourThirdIBPAxisPlanePairMultiplicity
        (ourSecondarySourceLabeled.hypercubicAct h) : ℚ) := by
  simp [ourThirdIBPAxisPlanePairOrbitMultiplicity, ourSecondarySourceSevenOrbit]

theorem ourThirdIBPAxisPlanePairOrbitMultiplicity_ourSecondarySwapped_action
    (h : Hypercubic4) :
    ourThirdIBPAxisPlanePairOrbitMultiplicity
      (ourSecondarySwappedSevenOrbit.hypercubicAct h) =
      (ourThirdIBPAxisPlanePairMultiplicity
        (ourSecondarySwappedLabeled.hypercubicAct h) : ℚ) := by
  simp [ourThirdIBPAxisPlanePairOrbitMultiplicity,
    ourSecondarySwappedSevenOrbit]

theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourSecondarySource :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSecondarySourceSevenOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourSecondarySourceSevenOrbit (1 : ℚ))) =
        ourSecondarySourceLabeled.tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            (ourSecondarySourceLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single,
      ourThirdIBPAxisPlanePairOrbitMultiplicity_ourSecondarySource_action]
    simp
  simp_rw [hterm]
  rw [ourSecondarySource_thirdIBPAxisPlanePairSignedWeight]
  norm_num

theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourSecondarySwapped :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSecondarySwappedSevenOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourSecondarySwappedSevenOrbit (1 : ℚ))) =
        ourSecondarySwappedLabeled.tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            (ourSecondarySwappedLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single,
      ourThirdIBPAxisPlanePairOrbitMultiplicity_ourSecondarySwapped_action]
    simp
  simp_rw [hterm]
  rw [ourSecondarySwapped_thirdIBPAxisPlanePairSignedWeight]
  norm_num

theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_secondary_fst :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2 ourSecondaryCoupledCommutatorVector.1) = 0 := by
  rw [ourSecondaryCoupledCommutatorVector_fst, LinearMap.map_sub,
    LinearMap.map_sub,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourSecondarySource,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourSecondarySwapped]
  norm_num

/-- The independently calibrated third coordinate vanishes on the secondary
source-seven commutator under both relation policies. -/
theorem ourInvariantThirdIBPAxisCoordinate_ourSecondaryCommutator
    (policy : PhysicalRelationPolicy) :
    ourInvariantThirdIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  unfold ourInvariantThirdIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSecondaryCommutator_full,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_secondary_fst]
  norm_num

/-! ## The repaired three-class map -/

/-- The prior cycle-profile correction is signed-`H(4)`-invariant.  This
local expansion exposes the two independently invariant contributions needed
by the three-class extension. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourCycleProfileInvariantTraceOrderCorrection
      (signedExactFieldRelabelOrbitAction h value) =
      ourCycleProfileInvariantTraceOrderCorrection value := by
  unfold ourCycleProfileInvariantTraceOrderCorrection
    ourTraceCycleProfileInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply]
  rw [ourThreeCoordinateInvariantTraceOrderCorrection_signed_action,
    ourInvariantTraceCycleProfileCoordinate_signed_action]

/-- OUR three-class extension of the cycle-profile correction.  The second
term repairs the secondary source-seven commutator, and the third term repairs
the exact second-IBP mismatch caused by that second term. -/
def ourThreeClassSourceSevenTraceOrderCorrection :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ourAugmentedCycleProfileInvariantTraceOrderCorrection +
    ourInvariantThirdIBPAxisCoordinate.smulRight ourSecondarySourceSevenResidual

theorem ourThreeClassSourceSevenTraceOrderCorrection_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (signedExactFieldRelabelOrbitAction h value) =
      ourThreeClassSourceSevenTraceOrderCorrection value := by
  unfold ourThreeClassSourceSevenTraceOrderCorrection
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smulRight_apply]
  rw [ourCycleProfileInvariantTraceOrderCorrection_signed_action,
    ourSecondaryPlaneProfileInvariantCoordinate_signed_action,
    ourInvariantThirdIBPAxisCoordinate_signed_action]

theorem ourThreeClassSourceSevenTraceOrderCorrection_exactFieldOrbitReynolds
    (value : ExactFieldRelabelOrbitSpace) :
    ourThreeClassSourceSevenTraceOrderCorrection (exactFieldOrbitReynolds value) =
      ourThreeClassSourceSevenTraceOrderCorrection value := by
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  simp_rw [ourThreeClassSourceSevenTraceOrderCorrection_signed_action]
  rw [Finset.sum_const, Finset.card_univ, Hypercubic4.card_hypercubic4]
  module

/-- The three-class correction retains the incoming source-seven commutator. -/
theorem ourThreeClassSourceSevenTraceOrderCorrection_ourCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  unfold ourThreeClassSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourCommutator_zero,
    ourInvariantThirdIBPAxisCoordinate_ourCommutator, zero_smul]
  simp

/-- The three-class correction retains the secondary source-seven
commutator. -/
theorem ourThreeClassSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
      0 := by
  unfold ourThreeClassSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourSecondaryCommutator_zero,
    ourInvariantThirdIBPAxisCoordinate_ourSecondaryCommutator, zero_smul]
  simp

/-- The third class cancels the exact two-class second-IBP mismatch. -/
theorem ourThreeClassSourceSevenTraceOrderCorrection_ourSecondIBP_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 := by
  unfold ourThreeClassSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourSecondIBP_eq_neg_residual,
    ourInvariantThirdIBPAxisCoordinate_ourSecondIBP]
  simp

/-- The three-class correction retains the first explicit IBP row. -/
theorem ourThreeClassSourceSevenTraceOrderCorrection_ourIBP_zero :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 := by
  unfold ourThreeClassSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourIBP_zero,
    ourInvariantThirdIBPAxisCoordinate_ourIBP, zero_smul]
  simp

/-- The three-class correction retains the listed Bianchi row. -/
theorem ourThreeClassSourceSevenTraceOrderCorrection_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  unfold ourThreeClassSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourBianchi_zero,
    ourInvariantThirdIBPAxisCoordinate_ourBianchi_zero, zero_smul]
  simp

/-- The three-class correction retains the listed on-shell EOM row. -/
theorem ourThreeClassSourceSevenTraceOrderCorrection_ourEOM_zero :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  unfold ourThreeClassSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourEOM_zero,
    ourInvariantThirdIBPAxisCoordinate_ourEOM_zero, zero_smul]
  simp

/-- The three-class correction retains the listed fundamental three-cut row. -/
theorem ourThreeClassSourceSevenTraceOrderCorrection_ourFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 := by
  unfold ourThreeClassSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero,
    ourInvariantThirdIBPAxisCoordinate_ourFundamentalThreeCut_zero, zero_smul]
  simp

/-- The three-class correction retains the listed polarized
trace-anticommutator row. -/
theorem ourThreeClassSourceSevenTraceOrderCorrection_ourTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 := by
  unfold ourThreeClassSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourTraceAnticommutator_zero,
    ourInvariantThirdIBPAxisCoordinate_ourTraceAnticommutator_zero, zero_smul]
  simp

/-- The three-class correction retains every lifted derivative-free field-eight
trace relation. -/
theorem ourThreeClassSourceSevenTraceOrderCorrection_liftedTraceGenerator_zero
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)) =
      0 := by
  unfold ourThreeClassSourceSevenTraceOrderCorrection
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_liftedTraceGenerator_zero]
  rw [show orbitPhysicalRelationOperator policy
      (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1) =
      fieldEightExactEmbed (fieldEightPhysicalTraceRow generator) by
        exact ourOrbitPhysicalRelationOperator_lift policy generator,
    ourInvariantThirdIBPAxisCoordinate_fieldEightExactEmbed_zero]
  simp

/-- Antisymmetry rows remain zero independently of all three selector terms. -/
theorem ourThreeClassSourceSevenTraceOrderCorrection_antisymmetry_zero
    (policy : PhysicalRelationPolicy)
    (carrier : RelationCarrier) (slot : Fin carrier.1.1)
    (coefficient : ℚ) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (.antisymmetry carrier slot) coefficient)) = 0 := by
  rw [orbitPhysicalRelationOperator_antisymmetry_zero]
  simp

/-! ## Coordinate-free invariant representatives -/

theorem ourThreeClassSourceSevenTraceOrderCorrection_invariantCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (ourInvariantCommutatorRow policy).1 = 0 := by
  rw [show (ourInvariantCommutatorRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) by rfl,
    ourThreeClassSourceSevenTraceOrderCorrection_exactFieldOrbitReynolds,
    ourThreeClassSourceSevenTraceOrderCorrection_ourCommutator_zero]

theorem ourThreeClassSourceSevenTraceOrderCorrection_invariantSecondIBP_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (ourInvariantSecondIBPRow policy).1 = 0 := by
  rw [show (ourInvariantSecondIBPRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) by rfl,
    ourThreeClassSourceSevenTraceOrderCorrection_exactFieldOrbitReynolds,
    ourThreeClassSourceSevenTraceOrderCorrection_ourSecondIBP_zero]

theorem ourThreeClassSourceSevenTraceOrderCorrection_invariantIBP_zero :
    ourThreeClassSourceSevenTraceOrderCorrection ourInvariantIBPRow.1 = 0 := by
  rw [show ourInvariantIBPRow.1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator .offShell
          (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) by rfl,
    ourThreeClassSourceSevenTraceOrderCorrection_exactFieldOrbitReynolds,
    ourThreeClassSourceSevenTraceOrderCorrection_ourIBP_zero]

theorem ourThreeClassSourceSevenTraceOrderCorrection_invariantBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (ourInvariantBianchiRow policy).1 = 0 := by
  rw [show (ourInvariantBianchiRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) by rfl,
    ourThreeClassSourceSevenTraceOrderCorrection_exactFieldOrbitReynolds,
    ourThreeClassSourceSevenTraceOrderCorrection_ourBianchi_zero]

theorem ourThreeClassSourceSevenTraceOrderCorrection_invariantEOM_zero :
    ourThreeClassSourceSevenTraceOrderCorrection ourInvariantEOMRow.1 = 0 := by
  rw [show ourInvariantEOMRow.1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator .onShell
          (Finsupp.single ourFieldSevenEOMGenerator 1)) by rfl,
    ourThreeClassSourceSevenTraceOrderCorrection_exactFieldOrbitReynolds,
    ourThreeClassSourceSevenTraceOrderCorrection_ourEOM_zero]

theorem ourThreeClassSourceSevenTraceOrderCorrection_invariantFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (ourInvariantFundamentalThreeCutRow policy).1 = 0 := by
  rw [show (ourInvariantFundamentalThreeCutRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) by rfl,
    ourThreeClassSourceSevenTraceOrderCorrection_exactFieldOrbitReynolds,
    ourThreeClassSourceSevenTraceOrderCorrection_ourFundamentalThreeCut_zero]

theorem ourThreeClassSourceSevenTraceOrderCorrection_invariantTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (ourInvariantTraceAnticommutatorRow policy).1 = 0 := by
  rw [show (ourInvariantTraceAnticommutatorRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) by rfl,
    ourThreeClassSourceSevenTraceOrderCorrection_exactFieldOrbitReynolds,
    ourThreeClassSourceSevenTraceOrderCorrection_ourTraceAnticommutator_zero]

theorem ourThreeClassSourceSevenTraceOrderCorrection_invariantLiftedTraceGenerator_zero
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1))) =
      0 := by
  rw [ourThreeClassSourceSevenTraceOrderCorrection_exactFieldOrbitReynolds,
    ourThreeClassSourceSevenTraceOrderCorrection_liftedTraceGenerator_zero]

#print axioms ourSecondarySource_thirdIBPAxisPlanePairSignedWeight
#print axioms ourInvariantThirdIBPAxisCoordinate_ourSecondaryCommutator
#print axioms ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourSecondIBP_ne_zero
#print axioms ourThreeClassSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero
#print axioms ourThreeClassSourceSevenTraceOrderCorrection_ourSecondIBP_zero
#print axioms ourThreeClassSourceSevenTraceOrderCorrection_ourFundamentalThreeCut_zero
#print axioms ourThreeClassSourceSevenTraceOrderCorrection_ourTraceAnticommutator_zero
#print axioms ourThreeClassSourceSevenTraceOrderCorrection_invariantEOM_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepair
