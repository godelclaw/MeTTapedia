import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileDifferential
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenCorrectionRefutation

/-!
# OUR two-class source-seven trace-order repair

The one-class correction is refuted by two concrete source-seven covariant
commutator rows with distinct derivative-plane profiles.  This module builds
two signed-`H(4)`-invariant finite selectors: one takes the incoming row to
one and the secondary row to zero, while the other has the opposite values.
They yield an exact repair of those two rows using their respective certified
eight-field trace classes.

This is an OUR bounded two-source repair.  It does not claim that the two
selectors annihilate the remaining physical relation generators, descend
through the full relation submodule, or construct Wilson-functional
coordinates.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair

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
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileDifferential
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenCorrectionRefutation

/-! ## A field-relabel-invariant derivative-word/plane profile -/

/-- OUR multiplicity of an ordered pair of distinct fields: the first has a
specified whole derivative word and plane, while the second has a specified
plane.  It keeps the two derivatives on their actual common field. -/
def ourDerivativeWordPlanePairMultiplicity (wordPlane : OrientedPlane)
    (word : List (Fin 4)) (otherPlane : OrientedPlane)
    (sector : LabeledLocalWordSector 7 2) : ℕ :=
  ∑ first : Fin 7, ∑ second : Fin 7,
    if first ≠ second ∧
        (sector.decoration.1 first).plane = wordPlane ∧
        List.ofFn (sector.decoration.1 first).derivativeAxis = word ∧
        (sector.decoration.1 second).plane = otherPlane
    then 1 else 0

/-- OUR profile count is unchanged by a uniform seven-field relabeling. -/
theorem ourDerivativeWordPlanePairMultiplicity_relabel
    (wordPlane : OrientedPlane) (word : List (Fin 4))
    (otherPlane : OrientedPlane) (rename : Equiv.Perm (Fin 7))
    (sector : LabeledLocalWordSector 7 2) :
    ourDerivativeWordPlanePairMultiplicity wordPlane word otherPlane
      (LabeledLocalWordSector.relabel rename sector) =
      ourDerivativeWordPlanePairMultiplicity wordPlane word otherPlane sector := by
  let indicator : Fin 7 → Fin 7 → ℕ := fun first second =>
    if first ≠ second ∧
        (sector.decoration.1 first).plane = wordPlane ∧
        List.ofFn (sector.decoration.1 first).derivativeAxis = word ∧
        (sector.decoration.1 second).plane = otherPlane
    then 1 else 0
  unfold ourDerivativeWordPlanePairMultiplicity
  have hterm (first second : Fin 7) :
      (if first ≠ second ∧
          ((LabeledLocalWordSector.relabel rename sector).decoration.1 first).plane =
            wordPlane ∧
          List.ofFn
              ((LabeledLocalWordSector.relabel rename sector).decoration.1 first).derivativeAxis = word ∧
          ((LabeledLocalWordSector.relabel rename sector).decoration.1 second).plane =
            otherPlane
        then 1 else 0) =
        indicator (rename.symm first) (rename.symm second) := by
    simp only [indicator, LabeledLocalWordSector.relabel,
      LocalWordDecoration.relabel]
    by_cases hne : first = second
    · subst second
      simp
    · have hrenamed : rename.symm first ≠ rename.symm second := by
        intro hequal
        exact hne (rename.symm.injective hequal)
      simp [hne, hrenamed]
  calc
    (∑ first, ∑ second,
      if first ≠ second ∧
          ((LabeledLocalWordSector.relabel rename sector).decoration.1 first).plane =
            wordPlane ∧
          List.ofFn
              ((LabeledLocalWordSector.relabel rename sector).decoration.1 first).derivativeAxis = word ∧
          ((LabeledLocalWordSector.relabel rename sector).decoration.1 second).plane =
            otherPlane
        then 1 else 0) =
      ∑ first, ∑ second, indicator (rename.symm first) second := by
        apply Finset.sum_congr rfl
        intro first _
        calc
          (∑ second,
            if first ≠ second ∧
                ((LabeledLocalWordSector.relabel rename sector).decoration.1 first).plane =
                  wordPlane ∧
                List.ofFn
                    ((LabeledLocalWordSector.relabel rename sector).decoration.1 first).derivativeAxis = word ∧
                ((LabeledLocalWordSector.relabel rename sector).decoration.1 second).plane =
                  otherPlane
              then 1 else 0) =
            ∑ second, indicator (rename.symm first) (rename.symm second) := by
              apply Finset.sum_congr rfl
              intro second _
              exact hterm first second
          _ = ∑ second, indicator (rename.symm first) second :=
            Equiv.sum_comp rename.symm
              (fun second => indicator (rename.symm first) second)
    _ = ∑ first, ∑ second, indicator first second :=
      Equiv.sum_comp rename.symm
        (fun first => ∑ second, indicator first second)

/-- OUR ordinary-orbit scalar for one chosen second plane. -/
def ourDerivativeWordPlanePairOrbitMultiplicity (otherPlane : OrientedPlane) :
    FieldSevenOrbitCarrier → ℚ :=
  Quotient.lift (fun sector =>
    (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
      otherPlane sector : ℚ)) (by
      intro left right horbit
      change MulAction.orbitRel (Equiv.Perm (Fin 7))
        (LabeledLocalWordSector 7 2) left right at horbit
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at horbit
      rcases horbit with ⟨rename, hrename⟩
      change LabeledLocalWordSector.relabel rename right = left at hrename
      rw [← hrename]
      exact_mod_cast ourDerivativeWordPlanePairMultiplicity_relabel
        (planeLookup 0 1) [0, 2] otherPlane rename right)

/-- OUR linear ordinary-orbit coordinate for one second plane. -/
def ourDerivativeWordPlanePairCoordinate (otherPlane : OrientedPlane) :
    FieldSevenOrbitSpace →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ
    (ourDerivativeWordPlanePairOrbitMultiplicity otherPlane)

@[simp] theorem ourDerivativeWordPlanePairCoordinate_single
    (otherPlane : OrientedPlane) (target : FieldSevenOrbitCarrier)
    (coefficient : ℚ) :
    ourDerivativeWordPlanePairCoordinate otherPlane
      (Finsupp.single target coefficient) =
      coefficient * ourDerivativeWordPlanePairOrbitMultiplicity otherPlane target := by
  simp [ourDerivativeWordPlanePairCoordinate]

theorem ourDerivativeWordPlanePairOrbitMultiplicity_action
    (otherPlane : OrientedPlane) (sector : LabeledLocalWordSector 7 2)
    (h : Hypercubic4) :
    ourDerivativeWordPlanePairOrbitMultiplicity otherPlane
      (FieldRelabelOrbitCarrier.hypercubicAct h (Quotient.mk _ sector)) =
      (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
        otherPlane (sector.hypercubicAct h) : ℚ) := by
  simp [ourDerivativeWordPlanePairOrbitMultiplicity]

/-! ## The complete secondary column -/

/-- OUR labeled seven-field source of the secondary covariant commutator. -/
abbrev ourSecondarySourceLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData ourSecondaryFieldSevenCommutatorCarrier.2)

/-- OUR labeled derivative-swapped secondary source. -/
abbrev ourSecondarySwappedLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData
      (swapExactDerivativePositions ourSecondaryFieldSevenCommutatorCarrier
        ourSecondaryFieldSevenCommutatorSite.outer
        ourSecondaryFieldSevenCommutatorSite.inner).2)

/-- OUR ordinary field-relabel orbit of the secondary source. -/
abbrev ourSecondarySourceSevenOrbit : FieldSevenOrbitCarrier :=
  Quotient.mk _ ourSecondarySourceLabeled

/-- OUR ordinary field-relabel orbit of the derivative-swapped secondary
source. -/
abbrev ourSecondarySwappedSevenOrbit : FieldSevenOrbitCarrier :=
  Quotient.mk _ ourSecondarySwappedLabeled

/-- OUR exact target of the secondary unswapped derivative source. -/
def ourSecondaryCommutatorSourceExactTarget : ExactFieldRelabelOrbitCarrier :=
  exactFieldRelabelOrbitOfOriented
    (exactNormalizedSectorData ourSecondaryFieldSevenCommutatorCarrier)

/-- OUR exact target of the secondary swapped derivative source. -/
def ourSecondaryCommutatorSwappedExactTarget : ExactFieldRelabelOrbitCarrier :=
  exactFieldRelabelOrbitOfOriented
    (exactNormalizedSectorData
      (swapExactDerivativePositions ourSecondaryFieldSevenCommutatorCarrier
        ourSecondaryFieldSevenCommutatorSite.outer
        ourSecondaryFieldSevenCommutatorSite.inner))

theorem ourSecondaryCommutator_source_orientationCoefficient :
    fieldAxisOrientationCoefficient
        (sectorFieldAxisAssignment ourSecondaryFieldSevenCommutatorCarrier.2) = 1 := by
  decide +kernel

theorem ourSecondaryCommutator_swapped_orientationCoefficient :
    fieldAxisOrientationCoefficient
        (sectorFieldAxisAssignment
          (swapExactDerivativePositions ourSecondaryFieldSevenCommutatorCarrier
            ourSecondaryFieldSevenCommutatorSite.outer
            ourSecondaryFieldSevenCommutatorSite.inner).2) = 1 := by
  decide +kernel

theorem orbitPhysicalRelationOperator_ourSecondaryCommutator_full
    (policy : PhysicalRelationPolicy) :
    orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1) =
      Finsupp.single ourSecondaryCommutatorSourceExactTarget 1 -
        Finsupp.single ourSecondaryCommutatorSwappedExactTarget 1 -
          Finsupp.single
            (ourSecondaryCommutatorInsertionExactTarget CurvatureInsertionSide.before) 1 +
            Finsupp.single
              (ourSecondaryCommutatorInsertionExactTarget CurvatureInsertionSide.after) 1 := by
  simp only [orbitPhysicalRelationOperator,
    normalizedPhysicalRelationOperator,
    LinearMap.comp_apply, physicalRelationOperator_single, one_smul,
    ourSecondaryFieldSevenCommutatorGenerator, physicalRelationRow,
    covariantCommutatorRow, map_sub, map_add,
    normalizeExactContextual_single]
  simp_rw [our_secondaryNormalizeExactContextualBasis_fieldRelabel]
  rw [exactFieldRelabelOrbitOfOriented_ourSecondaryCommutatorInsertion,
    exactFieldRelabelOrbitOfOriented_ourSecondaryCommutatorInsertion,
    ourSecondaryCommutator_source_orientationCoefficient,
    ourSecondaryCommutator_swapped_orientationCoefficient,
    ourSecondaryCommutator_before_orientationCoefficient,
    ourSecondaryCommutator_after_orientationCoefficient]
  rfl

/-- OUR two-band finite vector of the secondary covariant commutator. -/
def ourSecondaryCoupledCommutatorVector :
    FieldSevenOrbitSpace × FieldEightOrbitSpace :=
  exactFieldSevenEightProjectionBasis ourSecondaryCommutatorSourceExactTarget -
    exactFieldSevenEightProjectionBasis ourSecondaryCommutatorSwappedExactTarget -
      exactFieldSevenEightProjectionBasis
        (ourSecondaryCommutatorInsertionExactTarget CurvatureInsertionSide.before) +
        exactFieldSevenEightProjectionBasis
          (ourSecondaryCommutatorInsertionExactTarget CurvatureInsertionSide.after)

theorem exactFieldSevenEightProjection_ourSecondaryCommutator_full
    (policy : PhysicalRelationPolicy) :
    exactFieldSevenEightProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
      ourSecondaryCoupledCommutatorVector := by
  rw [orbitPhysicalRelationOperator_ourSecondaryCommutator_full]
  simp only [map_sub, map_add, exactFieldSevenEightProjection_single, one_smul]
  rfl

theorem exactFieldSevenProjection_ourSecondaryCommutator_full
    (policy : PhysicalRelationPolicy) :
    exactFieldSevenProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
      ourSecondaryCoupledCommutatorVector.1 := by
  change (exactFieldSevenEightProjection
    (orbitPhysicalRelationOperator policy
      (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1))).1 = _
  rw [exactFieldSevenEightProjection_ourSecondaryCommutator_full]

theorem ourSecondaryCommutatorSourceExactTarget_eq_seven :
    ourSecondaryCommutatorSourceExactTarget =
      (⟨ourSevenFieldCount, ourSecondarySourceSevenOrbit⟩ :
        ExactFieldRelabelOrbitCarrier) := rfl

theorem ourSecondaryCommutatorSwappedExactTarget_eq_seven :
    ourSecondaryCommutatorSwappedExactTarget =
      (⟨ourSevenFieldCount, ourSecondarySwappedSevenOrbit⟩ :
        ExactFieldRelabelOrbitCarrier) := rfl

theorem exactFieldSevenEightProjectionBasis_fst_of_secondaryInsertion
    (side : CurvatureInsertionSide) :
    (exactFieldSevenEightProjectionBasis
      (ourSecondaryCommutatorInsertionExactTarget side)).1 = 0 := by
  simp [exactFieldSevenEightProjectionBasis, ourSevenFieldCount,
    ourEightFieldCount]

theorem ourSecondaryCoupledCommutatorVector_fst :
    ourSecondaryCoupledCommutatorVector.1 =
      Finsupp.single ourSecondarySourceSevenOrbit 1 -
        Finsupp.single ourSecondarySwappedSevenOrbit 1 := by
  rw [ourSecondaryCoupledCommutatorVector,
    ourSecondaryCommutatorSourceExactTarget_eq_seven,
    ourSecondaryCommutatorSwappedExactTarget_eq_seven]
  rw [exactFieldSevenEightProjectionBasis_of_seven,
    exactFieldSevenEightProjectionBasis_of_seven]
  change Finsupp.single ourSecondarySourceSevenOrbit (1 : ℚ) -
      Finsupp.single ourSecondarySwappedSevenOrbit (1 : ℚ) -
      (exactFieldSevenEightProjectionBasis
        (ourSecondaryCommutatorInsertionExactTarget CurvatureInsertionSide.before)).1 +
      (exactFieldSevenEightProjectionBasis
        (ourSecondaryCommutatorInsertionExactTarget CurvatureInsertionSide.after)).1 = _
  rw [show (exactFieldSevenEightProjectionBasis
      (ourSecondaryCommutatorInsertionExactTarget CurvatureInsertionSide.before)).1 = 0 by
        exact exactFieldSevenEightProjectionBasis_fst_of_secondaryInsertion _,
    show (exactFieldSevenEightProjectionBasis
      (ourSecondaryCommutatorInsertionExactTarget CurvatureInsertionSide.after)).1 = 0 by
        exact exactFieldSevenEightProjectionBasis_fst_of_secondaryInsertion _]
  abel

/-! ## Kernel-reduced selector weights -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem incomingSource_incomingSelectorSignedWeight :
    (∑ h : Hypercubic4,
      sourceLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3) (sourceLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem incomingSwapped_incomingSelectorSignedWeight :
    (∑ h : Hypercubic4,
      swappedLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3) (swappedLabeled.hypercubicAct h) : ℚ)) = -16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem secondarySource_incomingSelectorSignedWeight :
    (∑ h : Hypercubic4,
      ourSecondarySourceLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3) (ourSecondarySourceLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem secondarySwapped_incomingSelectorSignedWeight :
    (∑ h : Hypercubic4,
      ourSecondarySwappedLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3) (ourSecondarySwappedLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem incomingSource_secondarySelectorSignedWeight :
    (∑ h : Hypercubic4,
      sourceLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2) (sourceLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem incomingSwapped_secondarySelectorSignedWeight :
    (∑ h : Hypercubic4,
      swappedLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2) (swappedLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem secondarySource_secondarySelectorSignedWeight :
    (∑ h : Hypercubic4,
      ourSecondarySourceLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2) (ourSecondarySourceLabeled.hypercubicAct h) : ℚ)) =
      16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem secondarySwapped_secondarySelectorSignedWeight :
    (∑ h : Hypercubic4,
      ourSecondarySwappedLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2) (ourSecondarySwappedLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

/-- OUR generic finite Reynolds computation for this profile coordinate. -/
theorem ourDerivativeWordPlanePairCoordinate_reynolds_single
    (otherPlane : OrientedPlane) (sector : LabeledLocalWordSector 7 2)
    (weight : ℚ)
    (hweight :
      (∑ h : Hypercubic4,
        sector.tensorSign h *
          (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
            otherPlane (sector.hypercubicAct h) : ℚ)) = weight) :
    ourDerivativeWordPlanePairCoordinate otherPlane
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (Quotient.mk _ sector : FieldSevenOrbitCarrier) (1 : ℚ))) =
      weight / 384 := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourDerivativeWordPlanePairCoordinate otherPlane
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (Quotient.mk _ sector : FieldSevenOrbitCarrier)
            (1 : ℚ))) =
        sector.tensorSign h *
          (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
            otherPlane (sector.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeWordPlanePairCoordinate_single,
      ourDerivativeWordPlanePairOrbitMultiplicity_action]
    simp
  simp_rw [hterm]
  rw [hweight]
  ring

/-! ## The rank-two selector matrix -/

set_option maxRecDepth 100000 in
theorem incomingSelectorCoordinate_reynolds_source :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single sourceSevenOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (Quotient.mk _ sourceLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) sourceLabeled 0
    incomingSource_incomingSelectorSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem incomingSelectorCoordinate_reynolds_swapped :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single swappedSevenOrbit (1 : ℚ))) = -(1 / 24 : ℚ) := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (Quotient.mk _ swappedLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = -(1 / 24 : ℚ)
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) swappedLabeled (-16)
    incomingSwapped_incomingSelectorSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem incomingSelectorCoordinate_reynolds_secondarySource :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSecondarySourceSevenOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourSecondarySourceLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) ourSecondarySourceLabeled 0
    secondarySource_incomingSelectorSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem incomingSelectorCoordinate_reynolds_secondarySwapped :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSecondarySwappedSevenOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourSecondarySwappedLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 1 3) ourSecondarySwappedLabeled 0
    secondarySwapped_incomingSelectorSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem secondarySelectorCoordinate_reynolds_source :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single sourceSevenOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (Quotient.mk _ sourceLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 0 2) sourceLabeled 0
    incomingSource_secondarySelectorSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem secondarySelectorCoordinate_reynolds_swapped :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single swappedSevenOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (Quotient.mk _ swappedLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 0 2) swappedLabeled 0
    incomingSwapped_secondarySelectorSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem secondarySelectorCoordinate_reynolds_secondarySource :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSecondarySourceSevenOrbit (1 : ℚ))) = 1 / 24 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourSecondarySourceLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 1 / 24
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 0 2) ourSecondarySourceLabeled 16
    secondarySource_secondarySelectorSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem secondarySelectorCoordinate_reynolds_secondarySwapped :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourSecondarySwappedSevenOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourSecondarySwappedLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 0 2) ourSecondarySwappedLabeled 0
    secondarySwapped_secondarySelectorSignedWeight]
  norm_num

theorem incomingSelectorCoordinate_reynolds_coupledIncoming_fst :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2 coupledIncomingCommutatorVector.1) = 1 / 24 := by
  rw [coupledIncomingCommutatorVector_fst, LinearMap.map_sub,
    LinearMap.map_sub, incomingSelectorCoordinate_reynolds_source,
    incomingSelectorCoordinate_reynolds_swapped]
  norm_num

theorem incomingSelectorCoordinate_reynolds_secondary_fst :
    ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)
      (sectorFieldOrbitReynolds 7 2 ourSecondaryCoupledCommutatorVector.1) = 0 := by
  rw [ourSecondaryCoupledCommutatorVector_fst, LinearMap.map_sub,
    LinearMap.map_sub, incomingSelectorCoordinate_reynolds_secondarySource,
    incomingSelectorCoordinate_reynolds_secondarySwapped]
  norm_num

theorem secondarySelectorCoordinate_reynolds_coupledIncoming_fst :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2 coupledIncomingCommutatorVector.1) = 0 := by
  rw [coupledIncomingCommutatorVector_fst, LinearMap.map_sub,
    LinearMap.map_sub, secondarySelectorCoordinate_reynolds_source,
    secondarySelectorCoordinate_reynolds_swapped]
  norm_num

theorem secondarySelectorCoordinate_reynolds_secondary_fst :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2 ourSecondaryCoupledCommutatorVector.1) =
      1 / 24 := by
  rw [ourSecondaryCoupledCommutatorVector_fst, LinearMap.map_sub,
    LinearMap.map_sub, secondarySelectorCoordinate_reynolds_secondarySource,
    secondarySelectorCoordinate_reynolds_secondarySwapped]
  norm_num

/-- OUR signed-invariant selector for the incoming source-seven plane profile. -/
def ourIncomingPlaneProfileInvariantCoordinate :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] ℚ :=
  (24 : ℚ) •
    ((ourDerivativeWordPlanePairCoordinate (planeLookup 1 3)).comp
      (exactFieldSevenProjection.comp exactFieldOrbitReynolds))

/-- OUR signed-invariant selector for the secondary source-seven plane profile. -/
def ourSecondaryPlaneProfileInvariantCoordinate :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] ℚ :=
  (24 : ℚ) •
    ((ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)).comp
      (exactFieldSevenProjection.comp exactFieldOrbitReynolds))

theorem ourIncomingPlaneProfileInvariantCoordinate_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourIncomingPlaneProfileInvariantCoordinate
      (signedExactFieldRelabelOrbitAction h value) =
      ourIncomingPlaneProfileInvariantCoordinate value := by
  unfold ourIncomingPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldOrbitReynolds_action]

theorem ourSecondaryPlaneProfileInvariantCoordinate_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourSecondaryPlaneProfileInvariantCoordinate
      (signedExactFieldRelabelOrbitAction h value) =
      ourSecondaryPlaneProfileInvariantCoordinate value := by
  unfold ourSecondaryPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldOrbitReynolds_action]

theorem ourIncomingPlaneProfileInvariantCoordinate_ourCommutator
    (policy : PhysicalRelationPolicy) :
    ourIncomingPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 1 := by
  unfold ourIncomingPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourCommutator_full,
    incomingSelectorCoordinate_reynolds_coupledIncoming_fst]
  norm_num

theorem ourIncomingPlaneProfileInvariantCoordinate_ourSecondaryCommutator
    (policy : PhysicalRelationPolicy) :
    ourIncomingPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  unfold ourIncomingPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSecondaryCommutator_full,
    incomingSelectorCoordinate_reynolds_secondary_fst]
  norm_num

theorem ourSecondaryPlaneProfileInvariantCoordinate_ourCommutator
    (policy : PhysicalRelationPolicy) :
    ourSecondaryPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  unfold ourSecondaryPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourCommutator_full,
    secondarySelectorCoordinate_reynolds_coupledIncoming_fst]
  norm_num

theorem ourSecondaryPlaneProfileInvariantCoordinate_ourSecondaryCommutator
    (policy : PhysicalRelationPolicy) :
    ourSecondaryPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
      1 := by
  unfold ourSecondaryPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSecondaryCommutator_full,
    secondarySelectorCoordinate_reynolds_secondary_fst]
  norm_num

/-! ## OUR exact two-source repair -/

/-- OUR bounded two-class correction. The incoming selector chooses the
previously certified incoming trace class and the secondary selector chooses
the distinct secondary trace class. -/
def ourTwoClassSourceSevenTraceOrderCorrection :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ourIncomingPlaneProfileInvariantCoordinate.smulRight
      literalIncomingCommutatorClass +
    ourSecondaryPlaneProfileInvariantCoordinate.smulRight
      ourSecondaryCommutatorClass -
    exactFieldEightTraceProjection

theorem ourTwoClassSourceSevenTraceOrderCorrection_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourTwoClassSourceSevenTraceOrderCorrection
      (signedExactFieldRelabelOrbitAction h value) =
      ourTwoClassSourceSevenTraceOrderCorrection value := by
  unfold ourTwoClassSourceSevenTraceOrderCorrection
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smulRight_apply]
  rw [ourIncomingPlaneProfileInvariantCoordinate_signed_action,
    ourSecondaryPlaneProfileInvariantCoordinate_signed_action,
    exactFieldEightTraceProjection_signed_action]

/-- OUR two-class correction annihilates the incoming concrete source-seven
covariant-commutator row for either physical policy. -/
theorem ourTwoClassSourceSevenTraceOrderCorrection_ourCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourTwoClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  unfold ourTwoClassSourceSevenTraceOrderCorrection
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
    ourIncomingPlaneProfileInvariantCoordinate_ourCommutator,
    ourSecondaryPlaneProfileInvariantCoordinate_ourCommutator,
    exactFieldEightTraceProjection_ourCommutator]
  simp

/-- OUR two-class correction annihilates the secondary concrete source-seven
covariant-commutator row for either physical policy. -/
theorem ourTwoClassSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourTwoClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
      0 := by
  unfold ourTwoClassSourceSevenTraceOrderCorrection
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
    ourIncomingPlaneProfileInvariantCoordinate_ourSecondaryCommutator,
    ourSecondaryPlaneProfileInvariantCoordinate_ourSecondaryCommutator,
    exactFieldEightTraceProjection_ourSecondaryCommutator]
  simp

#print axioms ourDerivativeWordPlanePairMultiplicity_relabel
#print axioms orbitPhysicalRelationOperator_ourSecondaryCommutator_full
#print axioms ourIncomingPlaneProfileInvariantCoordinate_ourCommutator
#print axioms ourSecondaryPlaneProfileInvariantCoordinate_ourSecondaryCommutator
#print axioms ourTwoClassSourceSevenTraceOrderCorrection_ourCommutator_zero
#print axioms ourTwoClassSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair
