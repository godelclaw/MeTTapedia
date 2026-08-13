import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantRepair

/-!
# OUR invariant trace-order Bianchi test

The two-coordinate signed-hypercubic trace-order correction repairs one
explicit integration-by-parts obstruction.  This module tests it on a genuine
three-distinct-axis innermost Bianchi row at the same field and derivative
degree.  The result below is an OUR finite relation-family check; it does not
assert annihilation of every Bianchi, EOM, IBP, or trace row.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantBianchi

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open SU2LatticeFDCensusNoGo
open HypercubicRawFDDimension16Census
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16AntisymmetryQuotient
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16DifferentialRelations
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16WilsonTraceOrderInvariantRepair

/-- OUR outer derivative position for the explicit Bianchi test carrier. -/
abbrev ourBianchiOuterPosition :
    Fin (dimension16DerivativeCount ourFieldSevenCommutatorCarrier.1) :=
  ⟨0, by
    norm_num [ourFieldSevenCommutatorCarrier, dimension16DerivativeCount]⟩

/-- OUR innermost derivative position for the explicit Bianchi test carrier. -/
abbrev ourBianchiPosition :
    Fin (dimension16DerivativeCount ourFieldSevenCommutatorCarrier.1) :=
  ⟨1, by
    norm_num [ourFieldSevenCommutatorCarrier, dimension16DerivativeCount]⟩

/-- OUR field selected for the Bianchi relation. -/
abbrev ourBianchiField : Fin 7 := ⟨0, by norm_num⟩

/-- OUR seven-field, two-derivative carrier whose Bianchi triple has distinct
axes `(0,1,2)` and whose outer derivative has axis `3`. -/
abbrev ourNondegenerateBianchiCarrier : RelationCarrier :=
  setFieldDerivativeAxes
    (setFieldDerivativeAxes ourFieldSevenCommutatorCarrier
      ⟨0, by change 0 < 7; norm_num⟩ ourBianchiOuterPosition 3 1 2)
    ⟨0, by change 0 < 7; norm_num⟩ ourBianchiPosition 0 1 2

/-- OUR named field and innermost position in the constructed carrier.  These
dependent indices keep the physical generator and its displayed summands
definitionally aligned. -/
abbrev ourNondegenerateBianchiField :
    Fin ourNondegenerateBianchiCarrier.1.1 :=
  ⟨0, by change 0 < 7; norm_num⟩

abbrev ourNondegenerateBianchiPosition :
    Fin (dimension16DerivativeCount ourNondegenerateBianchiCarrier.1) :=
  ⟨1, by
    norm_num [ourNondegenerateBianchiCarrier,
      ourFieldSevenCommutatorCarrier, setFieldDerivativeAxes,
      dimension16DerivativeCount]⟩

/-- OUR physical Bianchi generator, available under either relation policy. -/
def ourFieldSevenBianchiGenerator (policy : PhysicalRelationPolicy) :
    PhysicalRelationGenerator policy :=
  .bianchi ourNondegenerateBianchiCarrier
    ourNondegenerateBianchiField ourNondegenerateBianchiPosition (by
      constructor
      · rfl
      · intro deeper hdeeper
        exfalso
        change 1 < deeper.1 at hdeeper
        have hbound : deeper.1 < 2 := by
          simpa [ourNondegenerateBianchiCarrier,
            ourFieldSevenCommutatorCarrier, setFieldDerivativeAxes,
            dimension16DerivativeCount] using deeper.isLt
        omega)

/-- OUR three literal Bianchi summands, before contextual normalization. -/
abbrev ourBianchiBaseLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData ourNondegenerateBianchiCarrier.2)

abbrev ourBianchiRotateOneLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
      (normalizedSectorData
      (bianchiRotateOne ourNondegenerateBianchiCarrier
        ourNondegenerateBianchiField ourNondegenerateBianchiPosition).2)

abbrev ourBianchiRotateTwoLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
      (normalizedSectorData
      (bianchiRotateTwo ourNondegenerateBianchiCarrier
        ourNondegenerateBianchiField ourNondegenerateBianchiPosition).2)

/-- OUR ordinary seven-field relabel-orbit targets of the three summands. -/
abbrev ourBianchiBaseOrbit : FieldSevenOrbitCarrier :=
  Quotient.mk _ ourBianchiBaseLabeled

abbrev ourBianchiRotateOneOrbit : FieldSevenOrbitCarrier :=
  Quotient.mk _ ourBianchiRotateOneLabeled

abbrev ourBianchiRotateTwoOrbit : FieldSevenOrbitCarrier :=
  Quotient.mk _ ourBianchiRotateTwoLabeled

/-- OUR exact full-carrier targets of the three Bianchi summands. -/
abbrev ourBianchiBaseExactTarget : ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourBianchiBaseOrbit⟩

abbrev ourBianchiRotateOneExactTarget : ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourBianchiRotateOneOrbit⟩

abbrev ourBianchiRotateTwoExactTarget : ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourBianchiRotateTwoOrbit⟩

/-- The three exact contextual normalizations have their displayed targets. -/
theorem exactFieldRelabelOrbitOfOriented_ourBianchiBase :
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData ourNondegenerateBianchiCarrier) =
      ourBianchiBaseExactTarget := by
  rfl

theorem exactFieldRelabelOrbitOfOriented_ourBianchiRotateOne :
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData
        (bianchiRotateOne ourNondegenerateBianchiCarrier
          ourNondegenerateBianchiField ourNondegenerateBianchiPosition)) =
      ourBianchiRotateOneExactTarget := by
  rfl

theorem exactFieldRelabelOrbitOfOriented_ourBianchiRotateTwo :
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData
        (bianchiRotateTwo ourNondegenerateBianchiCarrier
          ourNondegenerateBianchiField ourNondegenerateBianchiPosition)) =
      ourBianchiRotateTwoExactTarget := by
  rfl

/- The following bounded computations are the orientation certificates for
the three concrete Bianchi summands. -/
set_option maxRecDepth 100000 in
theorem ourBianchiBaseOrientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment ourNondegenerateBianchiCarrier.2) = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourBianchiRotateOneOrientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment
        (bianchiRotateOne ourNondegenerateBianchiCarrier
          ourNondegenerateBianchiField ourNondegenerateBianchiPosition).2) =
      -1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourBianchiRotateTwoOrientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment
        (bianchiRotateTwo ourNondegenerateBianchiCarrier
          ourNondegenerateBianchiField ourNondegenerateBianchiPosition).2) =
      1 := by
  decide +kernel

/-- The three normalized Bianchi basis terms have their stated exact
full-carrier coordinates. -/
theorem ourNormalizeExactContextualBasis_ourBianchiBase :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis ourNondegenerateBianchiCarrier) =
      Finsupp.single ourBianchiBaseExactTarget 1 := by
  unfold normalizeExactContextualBasis
  rw [LinearMap.map_smul, normalizeExactFieldRelabel_single]
  unfold normalizeExactFieldRelabelBasis
  rw [exactFieldRelabelOrbitOfOriented_ourBianchiBase,
    ourBianchiBaseOrientationCoefficient]
  simp

theorem ourNormalizeExactContextualBasis_ourBianchiRotateOne :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (bianchiRotateOne ourNondegenerateBianchiCarrier
          ourNondegenerateBianchiField ourNondegenerateBianchiPosition)) =
      Finsupp.single ourBianchiRotateOneExactTarget (-1) := by
  unfold normalizeExactContextualBasis
  rw [LinearMap.map_smul, normalizeExactFieldRelabel_single]
  unfold normalizeExactFieldRelabelBasis
  rw [exactFieldRelabelOrbitOfOriented_ourBianchiRotateOne,
    ourBianchiRotateOneOrientationCoefficient]
  simp

theorem ourNormalizeExactContextualBasis_ourBianchiRotateTwo :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (bianchiRotateTwo ourNondegenerateBianchiCarrier
          ourNondegenerateBianchiField ourNondegenerateBianchiPosition)) =
      Finsupp.single ourBianchiRotateTwoExactTarget 1 := by
  unfold normalizeExactContextualBasis
  rw [LinearMap.map_smul, normalizeExactFieldRelabel_single]
  unfold normalizeExactFieldRelabelBasis
  rw [exactFieldRelabelOrbitOfOriented_ourBianchiRotateTwo,
    ourBianchiRotateTwoOrientationCoefficient]
  simp

/- The following six bounded sums are the finite certificate that both
invariant scalar coordinates vanish on all three Bianchi summands. -/
set_option maxRecDepth 100000 in
theorem ourBianchiBase_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourBianchiBaseLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourBianchiBaseLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourBianchiRotateOne_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourBianchiRotateOneLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourBianchiRotateOneLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourBianchiRotateTwo_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourBianchiRotateTwoLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourBianchiRotateTwoLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourBianchiBase_signedPlanePairWeight :
    (∑ h : Hypercubic4,
      ourBianchiBaseLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourBianchiBaseLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourBianchiRotateOne_signedPlanePairWeight :
    (∑ h : Hypercubic4,
      ourBianchiRotateOneLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourBianchiRotateOneLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourBianchiRotateTwo_signedPlanePairWeight :
    (∑ h : Hypercubic4,
      ourBianchiRotateTwoLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourBianchiRotateTwoLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

/-- The two raw coordinate functions follow the Bianchi orbit targets under
the signed hypercubic action. -/
theorem derivativeAxisOrbitMultiplicity_ourBianchiBase_action (h : Hypercubic4) :
    derivativeAxisOrbitMultiplicity [0, 2]
      (ourBianchiBaseOrbit.hypercubicAct h) =
      (derivativeAxisWordMultiplicity [0, 2]
        (ourBianchiBaseLabeled.hypercubicAct h) : ℚ) := by
  simp [derivativeAxisOrbitMultiplicity, ourBianchiBaseOrbit]

theorem derivativeAxisOrbitMultiplicity_ourBianchiRotateOne_action
    (h : Hypercubic4) :
    derivativeAxisOrbitMultiplicity [0, 2]
      (ourBianchiRotateOneOrbit.hypercubicAct h) =
      (derivativeAxisWordMultiplicity [0, 2]
        (ourBianchiRotateOneLabeled.hypercubicAct h) : ℚ) := by
  simp [derivativeAxisOrbitMultiplicity, ourBianchiRotateOneOrbit]

theorem derivativeAxisOrbitMultiplicity_ourBianchiRotateTwo_action
    (h : Hypercubic4) :
    derivativeAxisOrbitMultiplicity [0, 2]
      (ourBianchiRotateTwoOrbit.hypercubicAct h) =
      (derivativeAxisWordMultiplicity [0, 2]
        (ourBianchiRotateTwoLabeled.hypercubicAct h) : ℚ) := by
  simp [derivativeAxisOrbitMultiplicity, ourBianchiRotateTwoOrbit]

theorem ourIBPAxisPlanePairOrbitMultiplicity_ourBianchiBase_action
    (h : Hypercubic4) :
    ourIBPAxisPlanePairOrbitMultiplicity
      (ourBianchiBaseOrbit.hypercubicAct h) =
      (ourIBPAxisPlanePairMultiplicity
        (ourBianchiBaseLabeled.hypercubicAct h) : ℚ) := by
  simp [ourIBPAxisPlanePairOrbitMultiplicity, ourBianchiBaseOrbit]

theorem ourIBPAxisPlanePairOrbitMultiplicity_ourBianchiRotateOne_action
    (h : Hypercubic4) :
    ourIBPAxisPlanePairOrbitMultiplicity
      (ourBianchiRotateOneOrbit.hypercubicAct h) =
      (ourIBPAxisPlanePairMultiplicity
        (ourBianchiRotateOneLabeled.hypercubicAct h) : ℚ) := by
  simp [ourIBPAxisPlanePairOrbitMultiplicity, ourBianchiRotateOneOrbit]

theorem ourIBPAxisPlanePairOrbitMultiplicity_ourBianchiRotateTwo_action
    (h : Hypercubic4) :
    ourIBPAxisPlanePairOrbitMultiplicity
      (ourBianchiRotateTwoOrbit.hypercubicAct h) =
      (ourIBPAxisPlanePairMultiplicity
        (ourBianchiRotateTwoLabeled.hypercubicAct h) : ℚ) := by
  simp [ourIBPAxisPlanePairOrbitMultiplicity, ourBianchiRotateTwoOrbit]

/-- Both scalar orbit coordinates vanish after Reynolds averaging each
individual Bianchi summand. -/
theorem derivativeAxisCoordinate_reynolds_ourBianchiBase :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiBaseOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourBianchiBaseOrbit (1 : ℚ))) =
        ourBianchiBaseLabeled.tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            (ourBianchiBaseLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single,
      derivativeAxisOrbitMultiplicity_ourBianchiBase_action]
    simp [ourBianchiBaseOrbit]
  simp_rw [hterm]
  rw [ourBianchiBase_signedAxisWeight]
  norm_num

theorem derivativeAxisCoordinate_reynolds_ourBianchiRotateOne :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateOneOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourBianchiRotateOneOrbit (1 : ℚ))) =
        ourBianchiRotateOneLabeled.tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            (ourBianchiRotateOneLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single,
      derivativeAxisOrbitMultiplicity_ourBianchiRotateOne_action]
    simp [ourBianchiRotateOneOrbit]
  simp_rw [hterm]
  rw [ourBianchiRotateOne_signedAxisWeight]
  norm_num

theorem derivativeAxisCoordinate_reynolds_ourBianchiRotateTwo :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateTwoOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourBianchiRotateTwoOrbit (1 : ℚ))) =
        ourBianchiRotateTwoLabeled.tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            (ourBianchiRotateTwoLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single,
      derivativeAxisOrbitMultiplicity_ourBianchiRotateTwo_action]
    simp [ourBianchiRotateTwoOrbit]
  simp_rw [hterm]
  rw [ourBianchiRotateTwo_signedAxisWeight]
  norm_num

theorem ourIBPAxisPlanePairCoordinate_reynolds_ourBianchiBase :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiBaseOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourBianchiBaseOrbit (1 : ℚ))) =
        ourBianchiBaseLabeled.tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            (ourBianchiBaseLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single,
      ourIBPAxisPlanePairOrbitMultiplicity_ourBianchiBase_action]
    simp [ourBianchiBaseOrbit]
  simp_rw [hterm]
  rw [ourBianchiBase_signedPlanePairWeight]
  norm_num

theorem ourIBPAxisPlanePairCoordinate_reynolds_ourBianchiRotateOne :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateOneOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourBianchiRotateOneOrbit (1 : ℚ))) =
        ourBianchiRotateOneLabeled.tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            (ourBianchiRotateOneLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single,
      ourIBPAxisPlanePairOrbitMultiplicity_ourBianchiRotateOne_action]
    simp [ourBianchiRotateOneOrbit]
  simp_rw [hterm]
  rw [ourBianchiRotateOne_signedPlanePairWeight]
  norm_num

theorem ourIBPAxisPlanePairCoordinate_reynolds_ourBianchiRotateTwo :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateTwoOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourBianchiRotateTwoOrbit (1 : ℚ))) =
        ourBianchiRotateTwoLabeled.tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            (ourBianchiRotateTwoLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single,
      ourIBPAxisPlanePairOrbitMultiplicity_ourBianchiRotateTwo_action]
    simp [ourBianchiRotateTwoOrbit]
  simp_rw [hterm]
  rw [ourBianchiRotateTwo_signedPlanePairWeight]
  norm_num

/-- The middle Bianchi summand has coefficient `-1`; linearity transfers the
unit-coefficient zero calculations to that actual coefficient. -/
theorem derivativeAxisCoordinate_reynolds_ourBianchiRotateOne_neg :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateOneOrbit (-1 : ℚ))) = 0 := by
  rw [show Finsupp.single ourBianchiRotateOneOrbit (-1 : ℚ) =
      -Finsupp.single ourBianchiRotateOneOrbit (1 : ℚ) by simp,
    map_neg, map_neg, derivativeAxisCoordinate_reynolds_ourBianchiRotateOne]
  simp

theorem ourIBPAxisPlanePairCoordinate_reynolds_ourBianchiRotateOne_neg :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateOneOrbit (-1 : ℚ))) = 0 := by
  rw [show Finsupp.single ourBianchiRotateOneOrbit (-1 : ℚ) =
      -Finsupp.single ourBianchiRotateOneOrbit (1 : ℚ) by simp,
    map_neg, map_neg,
    ourIBPAxisPlanePairCoordinate_reynolds_ourBianchiRotateOne]
  simp

/-- Exact-field projections of an arbitrary seven-field orbit target. -/
theorem exactFieldSevenProjection_sevenTarget_single
    (orbit : FieldSevenOrbitCarrier) (coefficient : ℚ) :
    exactFieldSevenProjection
      (Finsupp.single (⟨ourSevenFieldCount, orbit⟩ :
        ExactFieldRelabelOrbitCarrier) coefficient) =
      Finsupp.single orbit coefficient := by
  change (exactFieldSevenEightProjection
    (Finsupp.single (⟨ourSevenFieldCount, orbit⟩ :
      ExactFieldRelabelOrbitCarrier) coefficient)).1 = _
  rw [exactFieldSevenEightProjection_single]
  simp [exactFieldSevenEightProjectionBasis,
    exactFieldSevenOrbitCast_self]

theorem exactFieldEightProjection_sevenTarget_single
    (orbit : FieldSevenOrbitCarrier) (coefficient : ℚ) :
    exactFieldEightProjection
      (Finsupp.single (⟨ourSevenFieldCount, orbit⟩ :
        ExactFieldRelabelOrbitCarrier) coefficient) = 0 := by
  rw [exactFieldEightProjection_single]
  simp [exactFieldEightProjectionBasis,
    ourSevenFieldCount, ourEightFieldCount]

/-- The actual orbit physical relation operator maps OUR Bianchi generator
to its three exact normalized summands. -/
theorem orbitPhysicalRelationOperator_ourBianchi
    (policy : PhysicalRelationPolicy) :
    orbitPhysicalRelationOperator policy
      (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1) =
      Finsupp.single ourBianchiBaseExactTarget 1 +
        Finsupp.single ourBianchiRotateOneExactTarget (-1) +
          Finsupp.single ourBianchiRotateTwoExactTarget 1 := by
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  simp only [one_smul, ourFieldSevenBianchiGenerator, physicalRelationRow,
    bianchiRow, map_add]
  rw [normalizeExactContextual_single, normalizeExactContextual_single,
    normalizeExactContextual_single]
  simp only [one_smul]
  rw [ourNormalizeExactContextualBasis_ourBianchiBase,
    ourNormalizeExactContextualBasis_ourBianchiRotateOne,
    ourNormalizeExactContextualBasis_ourBianchiRotateTwo]

/-- The seven-field projection of the actual Bianchi row has the same three
ordinary relabel-orbit summands. -/
theorem exactFieldSevenProjection_ourBianchi
    (policy : PhysicalRelationPolicy) :
    exactFieldSevenProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) =
      Finsupp.single ourBianchiBaseOrbit 1 +
        Finsupp.single ourBianchiRotateOneOrbit (-1) +
          Finsupp.single ourBianchiRotateTwoOrbit 1 := by
  rw [orbitPhysicalRelationOperator_ourBianchi, LinearMap.map_add,
    LinearMap.map_add,
    exactFieldSevenProjection_sevenTarget_single,
    exactFieldSevenProjection_sevenTarget_single,
    exactFieldSevenProjection_sevenTarget_single]

/-- The first invariant axis coordinate annihilates the full explicit Bianchi
row under both physical-relation policies. -/
theorem ourInvariantSevenAxisCoordinate_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  unfold ourInvariantSevenAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourBianchi]
  simp only [LinearMap.map_add,
    derivativeAxisCoordinate_reynolds_ourBianchiBase,
    derivativeAxisCoordinate_reynolds_ourBianchiRotateOne_neg,
    derivativeAxisCoordinate_reynolds_ourBianchiRotateTwo]
  norm_num

/-- The split-derivative/plane coordinate also annihilates the full explicit
Bianchi row under both physical-relation policies. -/
theorem ourInvariantIBPAxisCoordinate_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  unfold ourInvariantIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourBianchi]
  simp only [LinearMap.map_add,
    ourIBPAxisPlanePairCoordinate_reynolds_ourBianchiBase,
    ourIBPAxisPlanePairCoordinate_reynolds_ourBianchiRotateOne_neg,
    ourIBPAxisPlanePairCoordinate_reynolds_ourBianchiRotateTwo]
  norm_num

/-- The two-coordinate invariant seven-field functional annihilates the
explicit Bianchi row. -/
theorem ourTwoCoordinateInvariantSevenAxisCoordinate_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourTwoCoordinateInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  unfold ourTwoCoordinateInvariantSevenAxisCoordinate
  simp only [LinearMap.sub_apply, LinearMap.smul_apply,
    ourInvariantSevenAxisCoordinate_ourBianchi_zero,
    ourInvariantIBPAxisCoordinate_ourBianchi_zero]
  norm_num

/-- The field-eight component of the explicit seven-field Bianchi row is
zero before applying the trace-class map. -/
theorem exactFieldEightProjection_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    exactFieldEightProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  rw [orbitPhysicalRelationOperator_ourBianchi, LinearMap.map_add,
    LinearMap.map_add,
    exactFieldEightProjection_sevenTarget_single,
    exactFieldEightProjection_sevenTarget_single,
    exactFieldEightProjection_sevenTarget_single]
  simp

/-- The canonical eight-field trace coordinate vanishes on the explicit
seven-field Bianchi row. -/
theorem exactFieldEightTraceProjection_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    exactFieldEightTraceProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  change exactFieldEightTraceClassMap
    (exactFieldEightProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1))) = 0
  rw [exactFieldEightProjection_ourBianchi_zero]
  exact map_zero _

/-- The revised seven-field trace compensator annihilates the explicit Bianchi
row. -/
theorem ourTwoCoordinateInvariantSevenTraceCompensator_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourTwoCoordinateInvariantSevenTraceCompensator
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  simp only [ourTwoCoordinateInvariantSevenTraceCompensator,
    LinearMap.smulRight_apply,
    ourTwoCoordinateInvariantSevenAxisCoordinate_ourBianchi_zero,
    zero_smul]

/-- OUR two-coordinate invariant trace-order correction annihilates the full
explicit three-distinct-axis Bianchi row under either physical policy. -/
theorem ourTwoCoordinateInvariantTraceOrderCorrection_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  change ourTwoCoordinateInvariantSevenTraceCompensator
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) -
      exactFieldEightTraceProjection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0
  rw [ourTwoCoordinateInvariantSevenTraceCompensator_ourBianchi_zero,
    exactFieldEightTraceProjection_ourBianchi_zero]
  simp

/-- OUR signed-Reynolds invariant member represented by the explicit Bianchi
row under a chosen physical-relation policy. -/
def ourInvariantBianchiRow (policy : PhysicalRelationPolicy) :
    exactFieldOrbitInvariantSubmodule :=
  ⟨exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)),
    exactFieldOrbitReynolds_invariant _⟩

/-- The averaged explicit Bianchi row belongs to the honest coordinate-free
joint invariant relation submodule for its policy. -/
theorem ourInvariantBianchiRow_mem (policy : PhysicalRelationPolicy) :
    ourInvariantBianchiRow policy ∈ jointInvariantRelationSubmodule policy := by
  rw [mem_jointInvariantRelationSubmodule_iff]
  change exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) ∈
      orbitPhysicalRelationSubmodule policy
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  apply (orbitPhysicalRelationSubmodule policy).smul_mem
  apply Submodule.sum_mem
  intro h _
  apply orbitPhysicalRelationSubmodule_signed_invariant policy h
  exact ⟨Finsupp.single (ourFieldSevenBianchiGenerator policy) 1, rfl⟩

/-- The revised correction annihilates the actual invariant Bianchi member,
not merely its unaveraged presentation. -/
theorem ourTwoCoordinateInvariantTraceOrderCorrection_invariantBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (ourInvariantBianchiRow policy).1 = 0 := by
  rw [show (ourInvariantBianchiRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) by rfl,
    ourTwoCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourTwoCoordinateInvariantTraceOrderCorrection_ourBianchi_zero]

#print axioms ourBianchiBase_signedAxisWeight
#print axioms ourBianchiRotateOne_signedAxisWeight
#print axioms ourBianchiRotateTwo_signedAxisWeight
#print axioms ourBianchiBase_signedPlanePairWeight
#print axioms ourBianchiRotateOne_signedPlanePairWeight
#print axioms ourBianchiRotateTwo_signedPlanePairWeight
#print axioms ourTwoCoordinateInvariantTraceOrderCorrection_ourBianchi_zero
#print axioms ourInvariantBianchiRow_mem
#print axioms ourTwoCoordinateInvariantTraceOrderCorrection_invariantBianchi_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantBianchi
