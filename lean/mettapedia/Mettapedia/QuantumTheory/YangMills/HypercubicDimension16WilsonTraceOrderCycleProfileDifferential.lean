import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileRepair

/-!
# OUR cycle-profile compatibility for seven-field differential rows

The profile coordinate was introduced to repair a trace-order residual on
physical trace relations.  Before it can be used toward relation-submodule
descent, it must also be checked against the already realized non-trace
seven-field rows.  This module starts that finite compatibility calculation
with the full covariant-commutator row.  The source and swapped terms are
replayed over the signed hypercubic group with kernel reduction; their profile
weights both vanish.

This is OUR bounded compatibility calculation.  It does not claim a complete
physical `F,D` census or full descent through the joint relation submodule.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileDifferential

open V14HypercubicFDCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceInvariantWitness
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantBianchi
open HypercubicDimension16WilsonTraceOrderInvariantEOM
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced signed profile replay for the commutator source term. -/
theorem source_profileSignedWeight :
    (∑ h : Hypercubic4,
      sourceLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity (sourceLabeled.hypercubicAct h)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced signed profile replay for the swapped commutator term. -/
theorem swapped_profileSignedWeight :
    (∑ h : Hypercubic4,
      swappedLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity (swappedLabeled.hypercubicAct h)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The profile coordinate vanishes on the Reynolds average of the source
component of the actual covariant-commutator row. -/
theorem ourTraceCycleProfileAxisCoordinate_reynolds_source :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single sourceSevenOrbit (1 : ℚ))) = 0 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (Quotient.mk _ sourceLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single sourceLabeled 0
    source_profileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
/-- The profile coordinate vanishes on the Reynolds average of the swapped
component of the actual covariant-commutator row. -/
theorem ourTraceCycleProfileAxisCoordinate_reynolds_swapped :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single swappedSevenOrbit (1 : ℚ))) = 0 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (Quotient.mk _ swappedLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single swappedLabeled 0
    swapped_profileSignedWeight]
  norm_num

/-- The profile coordinate annihilates the full seven-field component of the
actual covariant-commutator row. -/
theorem ourTraceCycleProfileAxisCoordinate_reynolds_coupledIncoming_fst :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2 coupledIncomingCommutatorVector.1) = 0 := by
  rw [coupledIncomingCommutatorVector_fst, LinearMap.map_sub,
    LinearMap.map_sub,
    ourTraceCycleProfileAxisCoordinate_reynolds_source,
    ourTraceCycleProfileAxisCoordinate_reynolds_swapped]
  norm_num

/-- The signed-invariant profile coordinate vanishes on the full actual
covariant-commutator relation under either policy. -/
theorem ourInvariantTraceCycleProfileCoordinate_ourCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantTraceCycleProfileCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  unfold ourInvariantTraceCycleProfileCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourCommutator_full,
    ourTraceCycleProfileAxisCoordinate_reynolds_coupledIncoming_fst]
  norm_num

/-- The full profile correction retains the actual covariant-commutator
relation under either physical policy. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_ourCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  unfold ourCycleProfileInvariantTraceOrderCorrection
    ourTraceCycleProfileInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourCommutator_zero,
    ourInvariantTraceCycleProfileCoordinate_ourCommutator_zero]
  simp

/-! ### First integration by parts -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced signed profile replay for every summand of the first
physical integration-by-parts row. -/
theorem ourIBP_profileSignedWeight (field : Fin 7) :
    (∑ h : Hypercubic4,
      (ourIBPLabeledTerm field).tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          ((ourIBPLabeledTerm field).hypercubicAct h)) = 0 := by
  fin_cases field <;> decide +kernel

set_option maxRecDepth 100000 in
/-- The profile coordinate vanishes on every Reynolds-averaged first-IBP
summand. -/
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourIBP
    (field : Fin 7) :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (ourIBPOrbit field) (1 : ℚ))) = 0 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ (ourIBPLabeledTerm field) : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    (ourIBPLabeledTerm field) 0 (ourIBP_profileSignedWeight field)]
  norm_num

/-- The profile coordinate vanishes on the complete first-IBP row. -/
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourIBPRow :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (∑ field : Fin 7, Finsupp.single (ourIBPOrbit field) (1 : ℚ))) = 0 := by
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro field _
  exact ourTraceCycleProfileAxisCoordinate_reynolds_ourIBP field

/-- The signed-invariant profile coordinate vanishes on the actual first-IBP
relation. -/
theorem ourInvariantTraceCycleProfileCoordinate_ourIBP_zero :
    ourInvariantTraceCycleProfileCoordinate
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 := by
  unfold ourInvariantTraceCycleProfileCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourIBP,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourIBPRow]
  norm_num

/-- The full profile correction retains the actual first integration-by-parts
relation. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_ourIBP_zero :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 := by
  unfold ourCycleProfileInvariantTraceOrderCorrection
    ourTraceCycleProfileInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourIBP_zero,
    ourInvariantTraceCycleProfileCoordinate_ourIBP_zero]
  simp

/-! ### Second integration by parts -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced signed profile replay for every summand of the second
physical integration-by-parts row. -/
theorem ourSecondIBP_profileSignedWeight (field : Fin 7) :
    (∑ h : Hypercubic4,
      (ourSecondIBPLabeledTerm field).tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          ((ourSecondIBPLabeledTerm field).hypercubicAct h)) = 0 := by
  fin_cases field <;> decide +kernel

set_option maxRecDepth 100000 in
/-- The profile coordinate vanishes on every Reynolds-averaged second-IBP
summand. -/
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourSecondIBP
    (field : Fin 7) :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (ourSecondIBPOrbit field) (1 : ℚ))) = 0 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ (ourSecondIBPLabeledTerm field) : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    (ourSecondIBPLabeledTerm field) 0 (ourSecondIBP_profileSignedWeight field)]
  norm_num

/-- The profile coordinate vanishes on the complete second-IBP row. -/
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourSecondIBPRow :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (∑ field : Fin 7, Finsupp.single (ourSecondIBPOrbit field) (1 : ℚ))) =
      0 := by
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro field _
  exact ourTraceCycleProfileAxisCoordinate_reynolds_ourSecondIBP field

/-- The signed-invariant profile coordinate vanishes on the actual second-IBP
relation under either policy. -/
theorem ourInvariantTraceCycleProfileCoordinate_ourSecondIBP_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantTraceCycleProfileCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 := by
  unfold ourInvariantTraceCycleProfileCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSecondIBP,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourSecondIBPRow]
  norm_num

/-- The full profile correction retains the actual second integration-by-parts
relation under either physical policy. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_ourSecondIBP_zero
    (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 := by
  unfold ourCycleProfileInvariantTraceOrderCorrection
    ourTraceCycleProfileInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourSecondIBP_zero,
    ourInvariantTraceCycleProfileCoordinate_ourSecondIBP_zero]
  simp

/-! ### Bianchi -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced profile replay for the base term of the actual Bianchi
relation. -/
theorem ourBianchiBase_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourBianchiBaseLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourBianchiBaseLabeled.hypercubicAct h)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced profile replay for the first rotated Bianchi term. -/
theorem ourBianchiRotateOne_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourBianchiRotateOneLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourBianchiRotateOneLabeled.hypercubicAct h)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced profile replay for the second rotated Bianchi term. -/
theorem ourBianchiRotateTwo_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourBianchiRotateTwoLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourBianchiRotateTwoLabeled.hypercubicAct h)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The profile coordinate vanishes on the Reynolds-averaged Bianchi base
term. -/
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourBianchiBase :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiBaseOrbit (1 : ℚ))) = 0 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourBianchiBaseLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourBianchiBaseLabeled 0 ourBianchiBase_profileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
/-- The profile coordinate vanishes on the Reynolds-averaged first rotated
Bianchi term. -/
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourBianchiRotateOne :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateOneOrbit (1 : ℚ))) = 0 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourBianchiRotateOneLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourBianchiRotateOneLabeled 0 ourBianchiRotateOne_profileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
/-- The profile coordinate vanishes on the Reynolds-averaged second rotated
Bianchi term. -/
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourBianchiRotateTwo :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateTwoOrbit (1 : ℚ))) = 0 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourBianchiRotateTwoLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourBianchiRotateTwoLabeled 0 ourBianchiRotateTwo_profileSignedWeight]
  norm_num

/-- Linearity transfers the first rotated Bianchi computation to its actual
coefficient `-1`. -/
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourBianchiRotateOne_neg :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateOneOrbit (-1 : ℚ))) = 0 := by
  rw [show Finsupp.single ourBianchiRotateOneOrbit (-1 : ℚ) =
      -Finsupp.single ourBianchiRotateOneOrbit (1 : ℚ) by simp,
    map_neg, map_neg,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourBianchiRotateOne]
  simp

/-- The signed-invariant profile coordinate vanishes on the full physical
Bianchi row under either policy. -/
theorem ourInvariantTraceCycleProfileCoordinate_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantTraceCycleProfileCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  unfold ourInvariantTraceCycleProfileCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourBianchi]
  simp only [LinearMap.map_add,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourBianchiBase,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourBianchiRotateOne_neg,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourBianchiRotateTwo]
  norm_num

/-- The full profile correction retains the actual Bianchi relation under
either physical policy. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  unfold ourCycleProfileInvariantTraceOrderCorrection
    ourTraceCycleProfileInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourBianchi_zero,
    ourInvariantTraceCycleProfileCoordinate_ourBianchi_zero]
  simp

/-! ### On-shell equation of motion -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced profile replay for the first nonzero normalized EOM
summand. -/
theorem ourEOMZero_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourEOMZeroLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourEOMZeroLabeled.hypercubicAct h)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced profile replay for the second nonzero normalized EOM
summand. -/
theorem ourEOMOne_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourEOMOneLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourEOMOneLabeled.hypercubicAct h)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced profile replay for the third nonzero normalized EOM
summand. -/
theorem ourEOMThree_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourEOMThreeLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourEOMThreeLabeled.hypercubicAct h)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The profile coordinate vanishes on the first Reynolds-averaged nonzero
EOM summand. -/
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourEOMZero :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMZeroOrbit (1 : ℚ))) = 0 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourEOMZeroLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourEOMZeroLabeled 0 ourEOMZero_profileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
/-- The profile coordinate vanishes on the second Reynolds-averaged nonzero
EOM summand. -/
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourEOMOne :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMOneOrbit (1 : ℚ))) = 0 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourEOMOneLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourEOMOneLabeled 0 ourEOMOne_profileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
/-- The profile coordinate vanishes on the third Reynolds-averaged nonzero
EOM summand. -/
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourEOMThree :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMThreeOrbit (1 : ℚ))) = 0 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourEOMThreeLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourEOMThreeLabeled 0 ourEOMThree_profileSignedWeight]
  norm_num

/-- Linearity transfers the third EOM calculation to its actual coefficient
`-1`. -/
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourEOMThree_neg :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMThreeOrbit (-1 : ℚ))) = 0 := by
  rw [show Finsupp.single ourEOMThreeOrbit (-1 : ℚ) =
      -Finsupp.single ourEOMThreeOrbit (1 : ℚ) by simp,
    map_neg, map_neg,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourEOMThree]
  simp

/-- The signed-invariant profile coordinate vanishes on the complete actual
on-shell EOM relation. -/
theorem ourInvariantTraceCycleProfileCoordinate_ourEOM_zero :
    ourInvariantTraceCycleProfileCoordinate
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  unfold ourInvariantTraceCycleProfileCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourEOM]
  simp only [LinearMap.map_add,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourEOMZero,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourEOMOne,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourEOMThree_neg]
  norm_num

/-- The full profile correction retains the complete actual on-shell EOM
relation. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_ourEOM_zero :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  unfold ourCycleProfileInvariantTraceOrderCorrection
    ourTraceCycleProfileInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourEOM_zero,
    ourInvariantTraceCycleProfileCoordinate_ourEOM_zero]
  simp

/-! ### Coordinate-free invariant representatives -/

/-- The profile correction annihilates the actual Reynolds-averaged
commutator member of the coordinate-free relation submodule. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_invariantCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (ourInvariantCommutatorRow policy).1 = 0 := by
  rw [show (ourInvariantCommutatorRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) by rfl,
    ourCycleProfileInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourCycleProfileInvariantTraceOrderCorrection_ourCommutator_zero]

/-- The profile correction annihilates the actual Reynolds-averaged first
IBP member of the coordinate-free off-shell relation submodule. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_invariantIBP_zero :
    ourCycleProfileInvariantTraceOrderCorrection ourInvariantIBPRow.1 = 0 := by
  rw [show ourInvariantIBPRow.1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator .offShell
          (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) by rfl,
    ourCycleProfileInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourCycleProfileInvariantTraceOrderCorrection_ourIBP_zero]

/-- The profile correction annihilates the actual Reynolds-averaged second
IBP member of the coordinate-free relation submodule. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_invariantSecondIBP_zero
    (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (ourInvariantSecondIBPRow policy).1 = 0 := by
  rw [show (ourInvariantSecondIBPRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) by rfl,
    ourCycleProfileInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourCycleProfileInvariantTraceOrderCorrection_ourSecondIBP_zero]

/-- The profile correction annihilates the actual Reynolds-averaged Bianchi
member of the coordinate-free relation submodule. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_invariantBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (ourInvariantBianchiRow policy).1 = 0 := by
  rw [show (ourInvariantBianchiRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) by rfl,
    ourCycleProfileInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourCycleProfileInvariantTraceOrderCorrection_ourBianchi_zero]

/-- The profile correction annihilates the actual Reynolds-averaged on-shell
EOM member of the coordinate-free relation submodule. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_invariantEOM_zero :
    ourCycleProfileInvariantTraceOrderCorrection ourInvariantEOMRow.1 = 0 := by
  rw [show ourInvariantEOMRow.1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator .onShell
          (Finsupp.single ourFieldSevenEOMGenerator 1)) by rfl,
    ourCycleProfileInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourCycleProfileInvariantTraceOrderCorrection_ourEOM_zero]

#print axioms source_profileSignedWeight
#print axioms swapped_profileSignedWeight
#print axioms ourInvariantTraceCycleProfileCoordinate_ourCommutator_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_ourCommutator_zero
#print axioms ourIBP_profileSignedWeight
#print axioms ourInvariantTraceCycleProfileCoordinate_ourIBP_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_ourIBP_zero
#print axioms ourSecondIBP_profileSignedWeight
#print axioms ourInvariantTraceCycleProfileCoordinate_ourSecondIBP_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_ourSecondIBP_zero
#print axioms ourBianchiBase_profileSignedWeight
#print axioms ourBianchiRotateOne_profileSignedWeight
#print axioms ourBianchiRotateTwo_profileSignedWeight
#print axioms ourInvariantTraceCycleProfileCoordinate_ourBianchi_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_ourBianchi_zero
#print axioms ourEOMZero_profileSignedWeight
#print axioms ourEOMOne_profileSignedWeight
#print axioms ourEOMThree_profileSignedWeight
#print axioms ourInvariantTraceCycleProfileCoordinate_ourEOM_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_ourEOM_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_invariantCommutator_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_invariantIBP_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_invariantSecondIBP_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_invariantBianchi_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_invariantEOM_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileDifferential
