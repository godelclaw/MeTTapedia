import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantBianchi

/-!
# OUR invariant trace-order EOM test

The two-coordinate signed-hypercubic trace-order correction has passed an
explicit genuine Bianchi row.  This module tests the policy-specific next
relation: an on-shell equation-of-motion row.  The result is an OUR finite
relation-family check, not an assertion that every EOM, Bianchi, IBP, or trace
row is annihilated.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantEOM

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
open HypercubicDimension16WilsonTraceOrderInvariantBianchi

/-- OUR innermost-site certificate for the explicit on-shell EOM row. -/
theorem ourEOMInnermost :
    IsInnermostDerivative ourNondegenerateBianchiCarrier
      ourNondegenerateBianchiField ourNondegenerateBianchiPosition := by
  constructor
  · rfl
  · intro deeper hdeeper
    exfalso
    change 1 < deeper.1 at hdeeper
    have hbound : deeper.1 < 2 := by
      simpa [ourNondegenerateBianchiCarrier,
        ourFieldSevenCommutatorCarrier, setFieldDerivativeAxes,
        dimension16DerivativeCount] using deeper.isLt
    omega

/-- OUR explicit EOM generator, inhabited only in the on-shell policy. -/
def ourFieldSevenEOMGenerator : PhysicalRelationGenerator .onShell :=
  .eom rfl ourNondegenerateBianchiCarrier ourNondegenerateBianchiField
    ourNondegenerateBianchiPosition ourEOMInnermost

/-- The four contracted-index terms of OUR on-shell EOM row. -/
abbrev ourEOMZeroCarrier : RelationCarrier :=
  eomTerm ourNondegenerateBianchiCarrier ourNondegenerateBianchiField
    ourNondegenerateBianchiPosition 0

abbrev ourEOMOneCarrier : RelationCarrier :=
  eomTerm ourNondegenerateBianchiCarrier ourNondegenerateBianchiField
    ourNondegenerateBianchiPosition 1

abbrev ourEOMTwoCarrier : RelationCarrier :=
  eomTerm ourNondegenerateBianchiCarrier ourNondegenerateBianchiField
    ourNondegenerateBianchiPosition 2

abbrev ourEOMThreeCarrier : RelationCarrier :=
  eomTerm ourNondegenerateBianchiCarrier ourNondegenerateBianchiField
    ourNondegenerateBianchiPosition 3

/-- OUR labeled normalizations of the four EOM terms. -/
abbrev ourEOMZeroLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData ourEOMZeroCarrier.2)

abbrev ourEOMOneLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData ourEOMOneCarrier.2)

abbrev ourEOMTwoLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData ourEOMTwoCarrier.2)

abbrev ourEOMThreeLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData ourEOMThreeCarrier.2)

/-- OUR seven-field orbit targets of the EOM summands. -/
abbrev ourEOMZeroOrbit : FieldSevenOrbitCarrier := Quotient.mk _ ourEOMZeroLabeled
abbrev ourEOMOneOrbit : FieldSevenOrbitCarrier := Quotient.mk _ ourEOMOneLabeled
abbrev ourEOMTwoOrbit : FieldSevenOrbitCarrier := Quotient.mk _ ourEOMTwoLabeled
abbrev ourEOMThreeOrbit : FieldSevenOrbitCarrier := Quotient.mk _ ourEOMThreeLabeled

/-- OUR full-carrier targets of the EOM summands. -/
abbrev ourEOMZeroExactTarget : ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourEOMZeroOrbit⟩

abbrev ourEOMOneExactTarget : ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourEOMOneOrbit⟩

abbrev ourEOMTwoExactTarget : ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourEOMTwoOrbit⟩

abbrev ourEOMThreeExactTarget : ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourEOMThreeOrbit⟩

theorem exactFieldRelabelOrbitOfOriented_ourEOMZero :
    exactFieldRelabelOrbitOfOriented (exactNormalizedSectorData ourEOMZeroCarrier) =
      ourEOMZeroExactTarget := by rfl

theorem exactFieldRelabelOrbitOfOriented_ourEOMOne :
    exactFieldRelabelOrbitOfOriented (exactNormalizedSectorData ourEOMOneCarrier) =
      ourEOMOneExactTarget := by rfl

theorem exactFieldRelabelOrbitOfOriented_ourEOMTwo :
    exactFieldRelabelOrbitOfOriented (exactNormalizedSectorData ourEOMTwoCarrier) =
      ourEOMTwoExactTarget := by rfl

theorem exactFieldRelabelOrbitOfOriented_ourEOMThree :
    exactFieldRelabelOrbitOfOriented (exactNormalizedSectorData ourEOMThreeCarrier) =
      ourEOMThreeExactTarget := by rfl

/- The following four bounded computations certify the orientations of the
concrete EOM summands. -/
set_option maxRecDepth 100000 in
theorem ourEOMZeroOrientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment ourEOMZeroCarrier.2) = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourEOMOneOrientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment ourEOMOneCarrier.2) = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourEOMTwoOrientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment ourEOMTwoCarrier.2) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourEOMThreeOrientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment ourEOMThreeCarrier.2) = -1 := by
  decide +kernel

/-- Exact contextual normalization of the first EOM summand. -/
theorem ourNormalizeExactContextualBasis_ourEOMZero :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis ourEOMZeroCarrier) =
      Finsupp.single ourEOMZeroExactTarget 1 := by
  unfold normalizeExactContextualBasis
  rw [LinearMap.map_smul, normalizeExactFieldRelabel_single]
  unfold normalizeExactFieldRelabelBasis
  rw [exactFieldRelabelOrbitOfOriented_ourEOMZero,
    ourEOMZeroOrientationCoefficient]
  simp

/-- Exact contextual normalization of the second EOM summand. -/
theorem ourNormalizeExactContextualBasis_ourEOMOne :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis ourEOMOneCarrier) =
      Finsupp.single ourEOMOneExactTarget 1 := by
  unfold normalizeExactContextualBasis
  rw [LinearMap.map_smul, normalizeExactFieldRelabel_single]
  unfold normalizeExactFieldRelabelBasis
  rw [exactFieldRelabelOrbitOfOriented_ourEOMOne,
    ourEOMOneOrientationCoefficient]
  simp

/-- The diagonal field-strength EOM summand vanishes in exact normalization. -/
theorem ourNormalizeExactContextualBasis_ourEOMTwo :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis ourEOMTwoCarrier) = 0 := by
  unfold normalizeExactContextualBasis
  rw [LinearMap.map_smul, normalizeExactFieldRelabel_single]
  unfold normalizeExactFieldRelabelBasis
  rw [exactFieldRelabelOrbitOfOriented_ourEOMTwo,
    ourEOMTwoOrientationCoefficient]
  simp

/-- Exact contextual normalization of the fourth EOM summand. -/
theorem ourNormalizeExactContextualBasis_ourEOMThree :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis ourEOMThreeCarrier) =
      Finsupp.single ourEOMThreeExactTarget (-1) := by
  unfold normalizeExactContextualBasis
  rw [LinearMap.map_smul, normalizeExactFieldRelabel_single]
  unfold normalizeExactFieldRelabelBasis
  rw [exactFieldRelabelOrbitOfOriented_ourEOMThree,
    ourEOMThreeOrientationCoefficient]
  simp

/- The following eight bounded sums are the finite certificates that the two
invariant scalar coordinates vanish on every EOM summand. -/
set_option maxRecDepth 100000 in
theorem ourEOMZero_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourEOMZeroLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourEOMZeroLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourEOMOne_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourEOMOneLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourEOMOneLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourEOMTwo_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourEOMTwoLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourEOMTwoLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourEOMThree_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourEOMThreeLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourEOMThreeLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourEOMZero_signedPlanePairWeight :
    (∑ h : Hypercubic4,
      ourEOMZeroLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourEOMZeroLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourEOMOne_signedPlanePairWeight :
    (∑ h : Hypercubic4,
      ourEOMOneLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourEOMOneLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourEOMTwo_signedPlanePairWeight :
    (∑ h : Hypercubic4,
      ourEOMTwoLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourEOMTwoLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourEOMThree_signedPlanePairWeight :
    (∑ h : Hypercubic4,
      ourEOMThreeLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourEOMThreeLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

/-- The raw coordinate functions follow the nonzero EOM orbit targets under
the signed hypercubic action. -/
theorem derivativeAxisOrbitMultiplicity_ourEOMZero_action (h : Hypercubic4) :
    derivativeAxisOrbitMultiplicity [0, 2]
      (ourEOMZeroOrbit.hypercubicAct h) =
      (derivativeAxisWordMultiplicity [0, 2]
        (ourEOMZeroLabeled.hypercubicAct h) : ℚ) := by
  simp [derivativeAxisOrbitMultiplicity, ourEOMZeroOrbit]

theorem derivativeAxisOrbitMultiplicity_ourEOMOne_action (h : Hypercubic4) :
    derivativeAxisOrbitMultiplicity [0, 2]
      (ourEOMOneOrbit.hypercubicAct h) =
      (derivativeAxisWordMultiplicity [0, 2]
        (ourEOMOneLabeled.hypercubicAct h) : ℚ) := by
  simp [derivativeAxisOrbitMultiplicity, ourEOMOneOrbit]

theorem derivativeAxisOrbitMultiplicity_ourEOMThree_action (h : Hypercubic4) :
    derivativeAxisOrbitMultiplicity [0, 2]
      (ourEOMThreeOrbit.hypercubicAct h) =
      (derivativeAxisWordMultiplicity [0, 2]
        (ourEOMThreeLabeled.hypercubicAct h) : ℚ) := by
  simp [derivativeAxisOrbitMultiplicity, ourEOMThreeOrbit]

theorem ourIBPAxisPlanePairOrbitMultiplicity_ourEOMZero_action
    (h : Hypercubic4) :
    ourIBPAxisPlanePairOrbitMultiplicity
      (ourEOMZeroOrbit.hypercubicAct h) =
      (ourIBPAxisPlanePairMultiplicity
        (ourEOMZeroLabeled.hypercubicAct h) : ℚ) := by
  simp [ourIBPAxisPlanePairOrbitMultiplicity, ourEOMZeroOrbit]

theorem ourIBPAxisPlanePairOrbitMultiplicity_ourEOMOne_action
    (h : Hypercubic4) :
    ourIBPAxisPlanePairOrbitMultiplicity
      (ourEOMOneOrbit.hypercubicAct h) =
      (ourIBPAxisPlanePairMultiplicity
        (ourEOMOneLabeled.hypercubicAct h) : ℚ) := by
  simp [ourIBPAxisPlanePairOrbitMultiplicity, ourEOMOneOrbit]

theorem ourIBPAxisPlanePairOrbitMultiplicity_ourEOMThree_action
    (h : Hypercubic4) :
    ourIBPAxisPlanePairOrbitMultiplicity
      (ourEOMThreeOrbit.hypercubicAct h) =
      (ourIBPAxisPlanePairMultiplicity
        (ourEOMThreeLabeled.hypercubicAct h) : ℚ) := by
  simp [ourIBPAxisPlanePairOrbitMultiplicity, ourEOMThreeOrbit]

/-- Both scalar coordinates vanish after Reynolds averaging each nonzero
normalized EOM summand. -/
theorem derivativeAxisCoordinate_reynolds_ourEOMZero :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMZeroOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourEOMZeroOrbit (1 : ℚ))) =
        ourEOMZeroLabeled.tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            (ourEOMZeroLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single,
      derivativeAxisOrbitMultiplicity_ourEOMZero_action]
    simp [ourEOMZeroOrbit]
  simp_rw [hterm]
  rw [ourEOMZero_signedAxisWeight]
  norm_num

theorem derivativeAxisCoordinate_reynolds_ourEOMOne :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMOneOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourEOMOneOrbit (1 : ℚ))) =
        ourEOMOneLabeled.tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            (ourEOMOneLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single,
      derivativeAxisOrbitMultiplicity_ourEOMOne_action]
    simp [ourEOMOneOrbit]
  simp_rw [hterm]
  rw [ourEOMOne_signedAxisWeight]
  norm_num

theorem derivativeAxisCoordinate_reynolds_ourEOMThree :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMThreeOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourEOMThreeOrbit (1 : ℚ))) =
        ourEOMThreeLabeled.tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            (ourEOMThreeLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single,
      derivativeAxisOrbitMultiplicity_ourEOMThree_action]
    simp [ourEOMThreeOrbit]
  simp_rw [hterm]
  rw [ourEOMThree_signedAxisWeight]
  norm_num

theorem ourIBPAxisPlanePairCoordinate_reynolds_ourEOMZero :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMZeroOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourEOMZeroOrbit (1 : ℚ))) =
        ourEOMZeroLabeled.tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            (ourEOMZeroLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single,
      ourIBPAxisPlanePairOrbitMultiplicity_ourEOMZero_action]
    simp [ourEOMZeroOrbit]
  simp_rw [hterm]
  rw [ourEOMZero_signedPlanePairWeight]
  norm_num

theorem ourIBPAxisPlanePairCoordinate_reynolds_ourEOMOne :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMOneOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourEOMOneOrbit (1 : ℚ))) =
        ourEOMOneLabeled.tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            (ourEOMOneLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single,
      ourIBPAxisPlanePairOrbitMultiplicity_ourEOMOne_action]
    simp [ourEOMOneOrbit]
  simp_rw [hterm]
  rw [ourEOMOne_signedPlanePairWeight]
  norm_num

theorem ourIBPAxisPlanePairCoordinate_reynolds_ourEOMThree :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMThreeOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourEOMThreeOrbit (1 : ℚ))) =
        ourEOMThreeLabeled.tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            (ourEOMThreeLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single,
      ourIBPAxisPlanePairOrbitMultiplicity_ourEOMThree_action]
    simp [ourEOMThreeOrbit]
  simp_rw [hterm]
  rw [ourEOMThree_signedPlanePairWeight]
  norm_num

/-- The fourth EOM summand has coefficient `-1` after contextual
normalization; linearity transfers its unit-coefficient coordinate checks. -/
theorem derivativeAxisCoordinate_reynolds_ourEOMThree_neg :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMThreeOrbit (-1 : ℚ))) = 0 := by
  rw [show Finsupp.single ourEOMThreeOrbit (-1 : ℚ) =
      -Finsupp.single ourEOMThreeOrbit (1 : ℚ) by simp,
    map_neg, map_neg, derivativeAxisCoordinate_reynolds_ourEOMThree]
  simp

theorem ourIBPAxisPlanePairCoordinate_reynolds_ourEOMThree_neg :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMThreeOrbit (-1 : ℚ))) = 0 := by
  rw [show Finsupp.single ourEOMThreeOrbit (-1 : ℚ) =
      -Finsupp.single ourEOMThreeOrbit (1 : ℚ) by simp,
    map_neg, map_neg,
    ourIBPAxisPlanePairCoordinate_reynolds_ourEOMThree]
  simp

/-- The actual physical orbit relation operator maps OUR on-shell EOM
generator to its three nonzero exact normalized summands. -/
theorem orbitPhysicalRelationOperator_ourEOM :
    orbitPhysicalRelationOperator .onShell
      (Finsupp.single ourFieldSevenEOMGenerator 1) =
      Finsupp.single ourEOMZeroExactTarget 1 +
        Finsupp.single ourEOMOneExactTarget 1 +
          Finsupp.single ourEOMThreeExactTarget (-1) := by
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  simp only [one_smul, ourFieldSevenEOMGenerator, physicalRelationRow,
    eomRow, map_sum]
  simp only [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_zero, add_zero]
  rw [normalizeExactContextual_single, normalizeExactContextual_single,
    normalizeExactContextual_single, normalizeExactContextual_single]
  simp only [one_smul]
  have hOne :
      normalizeExactFieldRelabel
        (normalizeExactContextualBasis
          (eomTerm ourNondegenerateBianchiCarrier
            ourNondegenerateBianchiField ourNondegenerateBianchiPosition
            (Fin.succ 0))) = Finsupp.single ourEOMOneExactTarget 1 := by
    simpa [ourEOMOneCarrier] using ourNormalizeExactContextualBasis_ourEOMOne
  have hTwo :
      normalizeExactFieldRelabel
        (normalizeExactContextualBasis
          (eomTerm ourNondegenerateBianchiCarrier
            ourNondegenerateBianchiField ourNondegenerateBianchiPosition
            (Fin.succ 0).succ)) = 0 := by
    simpa [ourEOMTwoCarrier] using ourNormalizeExactContextualBasis_ourEOMTwo
  have hThree :
      normalizeExactFieldRelabel
        (normalizeExactContextualBasis
          (eomTerm ourNondegenerateBianchiCarrier
            ourNondegenerateBianchiField ourNondegenerateBianchiPosition
            (Fin.succ 0).succ.succ)) =
        Finsupp.single ourEOMThreeExactTarget (-1) := by
    simpa [ourEOMThreeCarrier] using
      ourNormalizeExactContextualBasis_ourEOMThree
  rw [ourNormalizeExactContextualBasis_ourEOMZero, hOne, hTwo, hThree]
  abel

/-- The seven-field projection of the physical on-shell EOM row. -/
theorem exactFieldSevenProjection_ourEOM :
    exactFieldSevenProjection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) =
      Finsupp.single ourEOMZeroOrbit 1 +
        Finsupp.single ourEOMOneOrbit 1 +
          Finsupp.single ourEOMThreeOrbit (-1) := by
  rw [orbitPhysicalRelationOperator_ourEOM, LinearMap.map_add,
    LinearMap.map_add,
    exactFieldSevenProjection_sevenTarget_single,
    exactFieldSevenProjection_sevenTarget_single,
    exactFieldSevenProjection_sevenTarget_single]

/-- The first invariant coordinate annihilates OUR complete explicit on-shell
EOM row. -/
theorem ourInvariantSevenAxisCoordinate_ourEOM_zero :
    ourInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  unfold ourInvariantSevenAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourEOM]
  simp only [LinearMap.map_add,
    derivativeAxisCoordinate_reynolds_ourEOMZero,
    derivativeAxisCoordinate_reynolds_ourEOMOne,
    derivativeAxisCoordinate_reynolds_ourEOMThree_neg]
  norm_num

/-- The split-derivative/plane coordinate also annihilates OUR complete
explicit on-shell EOM row. -/
theorem ourInvariantIBPAxisCoordinate_ourEOM_zero :
    ourInvariantIBPAxisCoordinate
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  unfold ourInvariantIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourEOM]
  simp only [LinearMap.map_add,
    ourIBPAxisPlanePairCoordinate_reynolds_ourEOMZero,
    ourIBPAxisPlanePairCoordinate_reynolds_ourEOMOne,
    ourIBPAxisPlanePairCoordinate_reynolds_ourEOMThree_neg]
  norm_num

/-- The two-coordinate seven-field functional annihilates OUR explicit EOM
row. -/
theorem ourTwoCoordinateInvariantSevenAxisCoordinate_ourEOM_zero :
    ourTwoCoordinateInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  unfold ourTwoCoordinateInvariantSevenAxisCoordinate
  simp only [LinearMap.sub_apply, LinearMap.smul_apply,
    ourInvariantSevenAxisCoordinate_ourEOM_zero,
    ourInvariantIBPAxisCoordinate_ourEOM_zero]
  norm_num

/-- The field-eight coordinate vanishes on the seven-field EOM row. -/
theorem exactFieldEightProjection_ourEOM_zero :
    exactFieldEightProjection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  rw [orbitPhysicalRelationOperator_ourEOM, LinearMap.map_add,
    LinearMap.map_add,
    exactFieldEightProjection_sevenTarget_single,
    exactFieldEightProjection_sevenTarget_single,
    exactFieldEightProjection_sevenTarget_single]
  simp

/-- The canonical eight-field trace coordinate vanishes on OUR EOM row. -/
theorem exactFieldEightTraceProjection_ourEOM_zero :
    exactFieldEightTraceProjection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  change exactFieldEightTraceClassMap
    (exactFieldEightProjection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1))) = 0
  rw [exactFieldEightProjection_ourEOM_zero]
  exact map_zero _

/-- The revised seven-field compensator annihilates OUR EOM row. -/
theorem ourTwoCoordinateInvariantSevenTraceCompensator_ourEOM_zero :
    ourTwoCoordinateInvariantSevenTraceCompensator
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  simp only [ourTwoCoordinateInvariantSevenTraceCompensator,
    LinearMap.smulRight_apply,
    ourTwoCoordinateInvariantSevenAxisCoordinate_ourEOM_zero,
    zero_smul]

/-- OUR two-coordinate invariant trace-order correction annihilates the
explicit on-shell EOM row. -/
theorem ourTwoCoordinateInvariantTraceOrderCorrection_ourEOM_zero :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  change ourTwoCoordinateInvariantSevenTraceCompensator
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) -
      exactFieldEightTraceProjection
        (orbitPhysicalRelationOperator .onShell
          (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0
  rw [ourTwoCoordinateInvariantSevenTraceCompensator_ourEOM_zero,
    exactFieldEightTraceProjection_ourEOM_zero]
  simp

/-- OUR signed-Reynolds invariant member represented by the explicit on-shell
EOM row. -/
def ourInvariantEOMRow : exactFieldOrbitInvariantSubmodule :=
  ⟨exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)),
    exactFieldOrbitReynolds_invariant _⟩

/-- The averaged explicit EOM row belongs to the honest coordinate-free
on-shell joint invariant relation submodule. -/
theorem ourInvariantEOMRow_mem :
    ourInvariantEOMRow ∈ jointInvariantRelationSubmodule .onShell := by
  rw [mem_jointInvariantRelationSubmodule_iff]
  change exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) ∈
      orbitPhysicalRelationSubmodule .onShell
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  apply (orbitPhysicalRelationSubmodule .onShell).smul_mem
  apply Submodule.sum_mem
  intro h _
  apply orbitPhysicalRelationSubmodule_signed_invariant .onShell h
  exact ⟨Finsupp.single ourFieldSevenEOMGenerator 1, rfl⟩

/-- The revised correction annihilates the actual invariant EOM member, not
only its unaveraged presentation. -/
theorem ourTwoCoordinateInvariantTraceOrderCorrection_invariantEOM_zero :
    ourTwoCoordinateInvariantTraceOrderCorrection ourInvariantEOMRow.1 = 0 := by
  rw [show ourInvariantEOMRow.1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator .onShell
          (Finsupp.single ourFieldSevenEOMGenerator 1)) by rfl,
    ourTwoCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourTwoCoordinateInvariantTraceOrderCorrection_ourEOM_zero]

#print axioms ourEOMZero_signedAxisWeight
#print axioms ourEOMOne_signedAxisWeight
#print axioms ourEOMTwo_signedAxisWeight
#print axioms ourEOMThree_signedAxisWeight
#print axioms ourEOMZero_signedPlanePairWeight
#print axioms ourEOMOne_signedPlanePairWeight
#print axioms ourEOMTwo_signedPlanePairWeight
#print axioms ourEOMThree_signedPlanePairWeight
#print axioms ourTwoCoordinateInvariantTraceOrderCorrection_ourEOM_zero
#print axioms ourInvariantEOMRow_mem
#print axioms ourTwoCoordinateInvariantTraceOrderCorrection_invariantEOM_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantEOM
