import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantEOM

/-!
# OUR three-coordinate invariant trace-order repair

The two-coordinate signed-hypercubic trace-order correction repairs one
explicit integration-by-parts row and passes the displayed Bianchi and EOM
tests.  This module constructs a second, structurally distinct IBP row and
proves that the two-coordinate correction has the exact nonzero value
`(1 / 2) • literalIncomingCommutatorClass` there.  It then adds a third,
field-relabel-invariant split-derivative/plane coordinate.  The third
coordinate cancels that exact obstruction while retaining the previously
certified commutator, first-IBP, Bianchi, EOM, and derivative-free trace
checks proved below.

This is an OUR finite repair family.  It does not assert descent through the
complete physical relation submodule or construction of a noncommutative
Wilson-functional analytic coordinate system.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair

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
open HypercubicDimension16IBPTraceRelations
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceProjection
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceInvariantWitness
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16FieldEightTracePhysicalLift
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantBianchi
open HypercubicDimension16WilsonTraceOrderInvariantEOM

/-- OUR two distinguished derivative positions for the second IBP carrier. -/
abbrev ourSecondIBPOuterPosition :
    Fin (dimension16DerivativeCount ourFieldSevenCommutatorCarrier.1) :=
  ⟨0, by
    norm_num [ourFieldSevenCommutatorCarrier, dimension16DerivativeCount]⟩

abbrev ourSecondIBPInnerPosition :
    Fin (dimension16DerivativeCount ourFieldSevenCommutatorCarrier.1) :=
  ⟨1, by
    norm_num [ourFieldSevenCommutatorCarrier, dimension16DerivativeCount]⟩

/-- OUR second seven-field IBP carrier.  Its distinguished field has plane
`(0,1)` and its two derivatives have the distinct axes `1` and `3`; this is
not the carrier used to calibrate the two-coordinate repair. -/
abbrev ourSecondIBPCarrier : RelationCarrier :=
  setFieldDerivativeAxes
    (setFieldDerivativeAxes ourFieldSevenCommutatorCarrier
      ⟨0, by change 0 < 7; norm_num⟩ ourSecondIBPOuterPosition 1 0 1)
    ⟨0, by change 0 < 7; norm_num⟩
    ⟨1, by change 1 < 2; norm_num⟩ 3 0 1

/-- OUR outermost derivative position in the second IBP carrier. -/
abbrev ourSecondIBPPosition :
    Fin (dimension16DerivativeCount ourSecondIBPCarrier.1) :=
  ⟨0, by
    norm_num [ourSecondIBPCarrier, ourFieldSevenCommutatorCarrier,
      setFieldDerivativeAxes, dimension16DerivativeCount]⟩

/-- OUR labeled second-IBP summand after the outer derivative is assigned to
one field. -/
abbrev ourSecondIBPLabeledTerm (field : Fin 7) : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData
      (setDerivativeOwner ourSecondIBPCarrier ourSecondIBPPosition field).2)

/-- OUR ordinary field-relabel orbit of one second-IBP summand. -/
abbrev ourSecondIBPOrbit (field : Fin 7) : FieldSevenOrbitCarrier :=
  Quotient.mk _ (ourSecondIBPLabeledTerm field)

/-- OUR exact full-carrier target of one second-IBP summand. -/
abbrev ourSecondIBPExactTarget (field : Fin 7) :
    ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourSecondIBPOrbit field⟩

/-- OUR genuine second integration-by-parts generator, available under either
physical relation policy. -/
def ourFieldSevenSecondIBPGenerator
    (policy : PhysicalRelationPolicy) : PhysicalRelationGenerator policy :=
  .integrationByParts ourSecondIBPCarrier ourSecondIBPPosition (by
    intro other
    change 0 ≤ other.1
    omega)

theorem exactFieldRelabelOrbitOfOriented_ourSecondIBPTerm
    (field : Fin 7) :
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData
        (setDerivativeOwner ourSecondIBPCarrier ourSecondIBPPosition field)) =
      ourSecondIBPExactTarget field := by
  rfl

/- The following bounded computations certify the orientations of the seven
second-IBP summands. -/
set_option maxRecDepth 100000 in
theorem ourSecondIBPOrientationCoefficient (field : Fin 7) :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment
        (setDerivativeOwner ourSecondIBPCarrier ourSecondIBPPosition field).2) =
      1 := by
  fin_cases field <;> decide +kernel

/-- Exact field-relabel normalization of every second-IBP summand. -/
theorem ourNormalizeExactContextualBasis_ourSecondIBPTerm
    (field : Fin 7) :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (setDerivativeOwner ourSecondIBPCarrier ourSecondIBPPosition field)) =
      Finsupp.single (ourSecondIBPExactTarget field) 1 := by
  unfold normalizeExactContextualBasis
  rw [LinearMap.map_smul, normalizeExactFieldRelabel_single]
  unfold normalizeExactFieldRelabelBasis
  rw [exactFieldRelabelOrbitOfOriented_ourSecondIBPTerm,
    ourSecondIBPOrientationCoefficient]
  simp

/-- The actual physical orbit relation operator maps OUR second IBP generator
to the seven normalized summands. -/
theorem orbitPhysicalRelationOperator_ourSecondIBP
    (policy : PhysicalRelationPolicy) :
    orbitPhysicalRelationOperator policy
      (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1) =
      ∑ field : Fin 7, Finsupp.single (ourSecondIBPExactTarget field) 1 := by
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  simp only [one_smul, ourFieldSevenSecondIBPGenerator,
    physicalRelationRow, integrationByPartsRow, map_sum]
  apply Finset.sum_congr rfl
  intro field _
  rw [normalizeExactContextual_single]
  simp only [one_smul]
  exact ourNormalizeExactContextualBasis_ourSecondIBPTerm field

/- These bounded sums are the exact two-coordinate obstruction certificate. -/
set_option maxRecDepth 100000 in
theorem ourSecondIBPSignedAxisWeight :
    (∑ field : Fin 7, ∑ h : Hypercubic4,
      (ourSecondIBPLabeledTerm field).tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          ((ourSecondIBPLabeledTerm field).hypercubicAct h) : ℚ)) = 32 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourSecondIBPOldPlanePairSignedWeight :
    (∑ field : Fin 7, ∑ h : Hypercubic4,
      (ourSecondIBPLabeledTerm field).tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          ((ourSecondIBPLabeledTerm field).hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

/-- OUR third split-derivative/plane multiplicity.  It distinguishes the
second IBP carrier from the commutator and first IBP calibration: an ordered
field pair carries planes `(0,1)` and `(1,3)` with derivative axes `3` and
`1`, respectively. -/
abbrev ourThirdIBPAxisPlanePairMultiplicity :
    LabeledLocalWordSector 7 2 → ℕ :=
  derivativeAxisPlanePairMultiplicity
    (planeLookup 0 1) (planeLookup 1 3) 3 1

/-- OUR third multiplicity descends through uniform seven-field relabeling. -/
def ourThirdIBPAxisPlanePairOrbitMultiplicity : FieldSevenOrbitCarrier → ℚ :=
  Quotient.lift (fun sector =>
    (ourThirdIBPAxisPlanePairMultiplicity sector : ℚ)) (by
      intro left right horbit
      change MulAction.orbitRel (Equiv.Perm (Fin 7))
        (LabeledLocalWordSector 7 2) left right at horbit
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at horbit
      rcases horbit with ⟨rename, hrename⟩
      change LabeledLocalWordSector.relabel rename right = left at hrename
      rw [← hrename]
      exact_mod_cast derivativeAxisPlanePairMultiplicity_relabel
        (planeLookup 0 1) (planeLookup 1 3) 3 1 rename right)

/-- OUR linear ordinary-orbit coordinate for the third pattern. -/
def ourThirdIBPAxisPlanePairCoordinate : FieldSevenOrbitSpace →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ ourThirdIBPAxisPlanePairOrbitMultiplicity

@[simp] theorem ourThirdIBPAxisPlanePairCoordinate_single
    (target : FieldSevenOrbitCarrier) (coefficient : ℚ) :
    ourThirdIBPAxisPlanePairCoordinate
      (Finsupp.single target coefficient) =
      coefficient * ourThirdIBPAxisPlanePairOrbitMultiplicity target := by
  simp [ourThirdIBPAxisPlanePairCoordinate]

/- This bounded sum is the third-coordinate calibration certificate. -/
set_option maxRecDepth 100000 in
theorem ourSecondIBPThirdPlanePairSignedWeight :
    (∑ field : Fin 7, ∑ h : Hypercubic4,
      (ourSecondIBPLabeledTerm field).tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          ((ourSecondIBPLabeledTerm field).hypercubicAct h) : ℚ)) = 16 := by
  decide +kernel

/-- The three raw coordinate functions follow the second-IBP orbit targets
under the signed hypercubic action. -/
theorem derivativeAxisOrbitMultiplicity_ourSecondIBP_action
    (field : Fin 7) (h : Hypercubic4) :
    derivativeAxisOrbitMultiplicity [0, 2]
      ((ourSecondIBPOrbit field).hypercubicAct h) =
      (derivativeAxisWordMultiplicity [0, 2]
        ((ourSecondIBPLabeledTerm field).hypercubicAct h) : ℚ) := by
  simp [derivativeAxisOrbitMultiplicity, ourSecondIBPOrbit]

theorem ourIBPAxisPlanePairOrbitMultiplicity_ourSecondIBP_action
    (field : Fin 7) (h : Hypercubic4) :
    ourIBPAxisPlanePairOrbitMultiplicity
      ((ourSecondIBPOrbit field).hypercubicAct h) =
      (ourIBPAxisPlanePairMultiplicity
        ((ourSecondIBPLabeledTerm field).hypercubicAct h) : ℚ) := by
  simp [ourIBPAxisPlanePairOrbitMultiplicity, ourSecondIBPOrbit]

theorem ourThirdIBPAxisPlanePairOrbitMultiplicity_ourSecondIBP_action
    (field : Fin 7) (h : Hypercubic4) :
    ourThirdIBPAxisPlanePairOrbitMultiplicity
      ((ourSecondIBPOrbit field).hypercubicAct h) =
      (ourThirdIBPAxisPlanePairMultiplicity
        ((ourSecondIBPLabeledTerm field).hypercubicAct h) : ℚ) := by
  simp [ourThirdIBPAxisPlanePairOrbitMultiplicity, ourSecondIBPOrbit]

/-- The first raw coordinate evaluates the Reynolds average of OUR full
second-IBP row to `1 / 12`. -/
theorem derivativeAxisCoordinate_reynolds_ourSecondIBP :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (∑ field : Fin 7, Finsupp.single (ourSecondIBPOrbit field) (1 : ℚ))) =
      1 / 12 := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (field : Fin 7) (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (ourSecondIBPOrbit field) (1 : ℚ))) =
        (ourSecondIBPLabeledTerm field).tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            ((ourSecondIBPLabeledTerm field).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single,
      derivativeAxisOrbitMultiplicity_ourSecondIBP_action]
    simp [ourSecondIBPOrbit]
  simp_rw [hterm]
  rw [← Finset.smul_sum, ourSecondIBPSignedAxisWeight]
  norm_num

/-- The original second coordinate vanishes on the Reynolds average of OUR
second-IBP row. -/
theorem ourIBPAxisPlanePairCoordinate_reynolds_ourSecondIBP :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (∑ field : Fin 7, Finsupp.single (ourSecondIBPOrbit field) (1 : ℚ))) =
      0 := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (field : Fin 7) (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (ourSecondIBPOrbit field) (1 : ℚ))) =
        (ourSecondIBPLabeledTerm field).tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            ((ourSecondIBPLabeledTerm field).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single,
      ourIBPAxisPlanePairOrbitMultiplicity_ourSecondIBP_action]
    simp [ourSecondIBPOrbit]
  simp_rw [hterm]
  rw [← Finset.smul_sum, ourSecondIBPOldPlanePairSignedWeight]
  norm_num

/-- The third raw coordinate evaluates the Reynolds average of OUR second-IBP
row to `1 / 24`. -/
theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourSecondIBP :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (∑ field : Fin 7, Finsupp.single (ourSecondIBPOrbit field) (1 : ℚ))) =
      1 / 24 := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (field : Fin 7) (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (ourSecondIBPOrbit field) (1 : ℚ))) =
        (ourSecondIBPLabeledTerm field).tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            ((ourSecondIBPLabeledTerm field).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single,
      ourThirdIBPAxisPlanePairOrbitMultiplicity_ourSecondIBP_action]
    simp [ourSecondIBPOrbit]
  simp_rw [hterm]
  rw [← Finset.smul_sum, ourSecondIBPThirdPlanePairSignedWeight]
  norm_num

/-- The exact seven-field projection of OUR second IBP row. -/
theorem exactFieldSevenProjection_ourSecondIBP
    (policy : PhysicalRelationPolicy) :
    exactFieldSevenProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) =
      ∑ field : Fin 7, Finsupp.single (ourSecondIBPOrbit field) 1 := by
  rw [orbitPhysicalRelationOperator_ourSecondIBP, map_sum]
  apply Finset.sum_congr rfl
  intro field _
  exact exactFieldSevenProjection_sevenTarget_single
    (ourSecondIBPOrbit field) 1

/-- The existing first invariant coordinate has value `1 / 2` on OUR second
IBP row. -/
theorem ourInvariantSevenAxisCoordinate_ourSecondIBP
    (policy : PhysicalRelationPolicy) :
    ourInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) =
      1 / 2 := by
  unfold ourInvariantSevenAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSecondIBP,
    derivativeAxisCoordinate_reynolds_ourSecondIBP]
  norm_num

/-- The original split-derivative/plane coordinate has value zero on OUR
second IBP row. -/
theorem ourInvariantIBPAxisCoordinate_ourSecondIBP
    (policy : PhysicalRelationPolicy) :
    ourInvariantIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 := by
  unfold ourInvariantIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSecondIBP,
    ourIBPAxisPlanePairCoordinate_reynolds_ourSecondIBP]
  norm_num

/-- The exact obstruction: the two-coordinate seven-field scalar has value
`1 / 2` on OUR second IBP row. -/
theorem ourTwoCoordinateInvariantSevenAxisCoordinate_ourSecondIBP
    (policy : PhysicalRelationPolicy) :
    ourTwoCoordinateInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) =
      1 / 2 := by
  unfold ourTwoCoordinateInvariantSevenAxisCoordinate
  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  rw [ourInvariantSevenAxisCoordinate_ourSecondIBP,
    ourInvariantIBPAxisCoordinate_ourSecondIBP]
  norm_num

/-- The field-eight projection vanishes on OUR seven-field second IBP row. -/
theorem exactFieldEightProjection_ourSecondIBP_zero
    (policy : PhysicalRelationPolicy) :
    exactFieldEightProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 := by
  rw [orbitPhysicalRelationOperator_ourSecondIBP, map_sum]
  apply Finset.sum_eq_zero
  intro field _
  exact exactFieldEightProjection_sevenTarget_single
    (ourSecondIBPOrbit field) 1

/-- The canonical eight-field trace coordinate vanishes on OUR second IBP
row. -/
theorem exactFieldEightTraceProjection_ourSecondIBP_zero
    (policy : PhysicalRelationPolicy) :
    exactFieldEightTraceProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 := by
  change exactFieldEightTraceClassMap
    (exactFieldEightProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1))) = 0
  rw [exactFieldEightProjection_ourSecondIBP_zero]
  exact map_zero _

/-- The existing two-coordinate correction takes the exact nonzero value
`(1 / 2) • literalIncomingCommutatorClass` on OUR second IBP row. -/
theorem ourTwoCoordinateInvariantTraceOrderCorrection_ourSecondIBP
    (policy : PhysicalRelationPolicy) :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) =
      (1 / 2 : ℚ) • literalIncomingCommutatorClass := by
  change ourTwoCoordinateInvariantSevenTraceCompensator
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) -
      exactFieldEightTraceProjection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = _
  simp only [ourTwoCoordinateInvariantSevenTraceCompensator,
    LinearMap.smulRight_apply,
    ourTwoCoordinateInvariantSevenAxisCoordinate_ourSecondIBP,
    exactFieldEightTraceProjection_ourSecondIBP_zero, sub_zero]

/-- The two-coordinate correction therefore fails on the genuine second IBP
row. -/
theorem ourTwoCoordinateInvariantTraceOrderCorrection_ourSecondIBP_ne_zero
    (policy : PhysicalRelationPolicy) :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) ≠ 0 := by
  rw [ourTwoCoordinateInvariantTraceOrderCorrection_ourSecondIBP]
  exact smul_ne_zero (by norm_num) literalIncomingCommutatorClass_ne_zero

/-- OUR scaled invariant third coordinate.  Its scale `24` makes its value on
the second IBP row equal to one. -/
def ourInvariantThirdIBPAxisCoordinate :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] ℚ :=
  (24 : ℚ) •
    ((ourThirdIBPAxisPlanePairCoordinate.comp
      (exactFieldSevenProjection.comp exactFieldOrbitReynolds)))

/-- OUR third invariant coordinate is unchanged by every signed hypercubic
action. -/
theorem ourInvariantThirdIBPAxisCoordinate_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourInvariantThirdIBPAxisCoordinate
      (signedExactFieldRelabelOrbitAction h value) =
      ourInvariantThirdIBPAxisCoordinate value := by
  unfold ourInvariantThirdIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldOrbitReynolds_action]

/-- The third invariant coordinate has the calibration value one on OUR
second IBP row. -/
theorem ourInvariantThirdIBPAxisCoordinate_ourSecondIBP
    (policy : PhysicalRelationPolicy) :
    ourInvariantThirdIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 1 := by
  unfold ourInvariantThirdIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSecondIBP,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourSecondIBP]
  norm_num

/-- OUR third scalar contribution, valued in the incoming trace class. -/
def ourThirdInvariantTraceContribution :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ((1 / 2 : ℚ) • ourInvariantThirdIBPAxisCoordinate).smulRight
    literalIncomingCommutatorClass

/-- OUR three-coordinate trace-order correction adds the third invariant
contribution to the two-coordinate correction. -/
def ourThreeCoordinateInvariantTraceOrderCorrection :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ourTwoCoordinateInvariantTraceOrderCorrection - ourThirdInvariantTraceContribution

/-- The third contribution exactly cancels the certified second-IBP
obstruction. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_ourSecondIBP_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 := by
  unfold ourThreeCoordinateInvariantTraceOrderCorrection
    ourThirdInvariantTraceContribution
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourTwoCoordinateInvariantTraceOrderCorrection_ourSecondIBP,
    ourInvariantThirdIBPAxisCoordinate_ourSecondIBP]
  simp

/- The next three bounded certificates show that the third coordinate retains
the previously checked commutator and first-IBP calibration. -/
set_option maxRecDepth 100000 in
theorem ourIBPThirdPlanePairSignedWeight :
    (∑ field : Fin 7, ∑ h : Hypercubic4,
      (ourIBPLabeledTerm field).tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          ((ourIBPLabeledTerm field).hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem source_ourThirdIBPAxisPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      sourceLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (sourceLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem swapped_ourThirdIBPAxisPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      swappedLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (swappedLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

theorem ourThirdIBPAxisPlanePairOrbitMultiplicity_ourIBP_action
    (field : Fin 7) (h : Hypercubic4) :
    ourThirdIBPAxisPlanePairOrbitMultiplicity
      ((ourIBPOrbit field).hypercubicAct h) =
      (ourThirdIBPAxisPlanePairMultiplicity
        ((ourIBPLabeledTerm field).hypercubicAct h) : ℚ) := by
  simp [ourThirdIBPAxisPlanePairOrbitMultiplicity, ourIBPOrbit]

theorem ourThirdIBPAxisPlanePairOrbitMultiplicity_source_action
    (h : Hypercubic4) :
    ourThirdIBPAxisPlanePairOrbitMultiplicity
      (sourceSevenOrbit.hypercubicAct h) =
      (ourThirdIBPAxisPlanePairMultiplicity
        (sourceLabeled.hypercubicAct h) : ℚ) := by
  simp [ourThirdIBPAxisPlanePairOrbitMultiplicity, sourceSevenOrbit]

theorem ourThirdIBPAxisPlanePairOrbitMultiplicity_swapped_action
    (h : Hypercubic4) :
    ourThirdIBPAxisPlanePairOrbitMultiplicity
      (swappedSevenOrbit.hypercubicAct h) =
      (ourThirdIBPAxisPlanePairMultiplicity
        (swappedLabeled.hypercubicAct h) : ℚ) := by
  simp [ourThirdIBPAxisPlanePairOrbitMultiplicity, swappedSevenOrbit]

/-- The third raw coordinate vanishes on the Reynolds average of the first
explicit IBP row. -/
theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourIBP :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (∑ field : Fin 7, Finsupp.single (ourIBPOrbit field) (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (field : Fin 7) (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (ourIBPOrbit field) (1 : ℚ))) =
        (ourIBPLabeledTerm field).tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            ((ourIBPLabeledTerm field).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single,
      ourThirdIBPAxisPlanePairOrbitMultiplicity_ourIBP_action]
    simp [ourIBPOrbit]
  simp_rw [hterm]
  rw [← Finset.smul_sum, ourIBPThirdPlanePairSignedWeight]
  norm_num

/-- The third raw coordinate vanishes on each commutator source summand after
Reynolds averaging. -/
theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_source :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single sourceSevenOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single sourceSevenOrbit (1 : ℚ))) =
        sourceLabeled.tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            (sourceLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single,
      ourThirdIBPAxisPlanePairOrbitMultiplicity_source_action]
    simp [sourceSevenOrbit]
  simp_rw [hterm]
  rw [source_ourThirdIBPAxisPlanePairSignedWeight]
  norm_num

theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_swapped :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single swappedSevenOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single swappedSevenOrbit (1 : ℚ))) =
        swappedLabeled.tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            (swappedLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single,
      ourThirdIBPAxisPlanePairOrbitMultiplicity_swapped_action]
    simp [swappedSevenOrbit]
  simp_rw [hterm]
  rw [swapped_ourThirdIBPAxisPlanePairSignedWeight]
  norm_num

theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_coupledIncoming_fst :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2 coupledIncomingCommutatorVector.1) = 0 := by
  rw [coupledIncomingCommutatorVector_fst, LinearMap.map_sub,
    LinearMap.map_sub,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_source,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_swapped]
  norm_num

/-- The third invariant coordinate vanishes on the full concrete commutator
column for either policy. -/
theorem ourInvariantThirdIBPAxisCoordinate_ourCommutator
    (policy : PhysicalRelationPolicy) :
    ourInvariantThirdIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  unfold ourInvariantThirdIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourCommutator_full,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_coupledIncoming_fst]
  norm_num

/-- The third invariant coordinate vanishes on the original explicit IBP
row. -/
theorem ourInvariantThirdIBPAxisCoordinate_ourIBP :
    ourInvariantThirdIBPAxisCoordinate
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 := by
  unfold ourInvariantThirdIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourIBP,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourIBP]
  norm_num

/-- The third invariant coordinate vanishes on derivative-free eight-field
inclusions. -/
theorem ourInvariantThirdIBPAxisCoordinate_fieldEightExactEmbed_zero
    (value : FieldEightOrbitSpace) :
    ourInvariantThirdIBPAxisCoordinate (fieldEightExactEmbed value) = 0 := by
  unfold ourInvariantThirdIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_fieldEightExactEmbed]
  simp

/-- The three-coordinate correction retains the full concrete commutator
check. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_ourCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  unfold ourThreeCoordinateInvariantTraceOrderCorrection
    ourThirdInvariantTraceContribution
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourTwoCoordinateInvariantTraceOrderCorrection_ourCommutator_zero,
    ourInvariantThirdIBPAxisCoordinate_ourCommutator]
  simp

/-- The three-coordinate correction retains the original explicit IBP check. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_ourIBP_zero :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 := by
  unfold ourThreeCoordinateInvariantTraceOrderCorrection
    ourThirdInvariantTraceContribution
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourTwoCoordinateInvariantTraceOrderCorrection_ourIBP_zero,
    ourInvariantThirdIBPAxisCoordinate_ourIBP]
  simp

/-- The three-coordinate correction retains every lifted derivative-free
eight-field trace check. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_liftedTraceGenerator_zero
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)) =
      0 := by
  unfold ourThreeCoordinateInvariantTraceOrderCorrection
    ourThirdInvariantTraceContribution
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourTwoCoordinateInvariantTraceOrderCorrection_liftedTraceGenerator_zero]
  rw [show orbitPhysicalRelationOperator policy
      (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1) =
      fieldEightExactEmbed (fieldEightPhysicalTraceRow generator) by
        exact ourOrbitPhysicalRelationOperator_lift policy generator,
    ourInvariantThirdIBPAxisCoordinate_fieldEightExactEmbed_zero]
  simp

/- The following three bounded certificates test the new third coordinate on
the three distinct-axis Bianchi summands already used for the two-coordinate
repair. -/
set_option maxRecDepth 100000 in
theorem ourBianchiBase_signedThirdPlanePairWeight :
    (∑ h : Hypercubic4,
      ourBianchiBaseLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourBianchiBaseLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourBianchiRotateOne_signedThirdPlanePairWeight :
    (∑ h : Hypercubic4,
      ourBianchiRotateOneLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourBianchiRotateOneLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourBianchiRotateTwo_signedThirdPlanePairWeight :
    (∑ h : Hypercubic4,
      ourBianchiRotateTwoLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourBianchiRotateTwoLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

theorem ourThirdIBPAxisPlanePairOrbitMultiplicity_ourBianchiBase_action
    (h : Hypercubic4) :
    ourThirdIBPAxisPlanePairOrbitMultiplicity
      (ourBianchiBaseOrbit.hypercubicAct h) =
      (ourThirdIBPAxisPlanePairMultiplicity
        (ourBianchiBaseLabeled.hypercubicAct h) : ℚ) := by
  simp [ourThirdIBPAxisPlanePairOrbitMultiplicity, ourBianchiBaseOrbit]

theorem ourThirdIBPAxisPlanePairOrbitMultiplicity_ourBianchiRotateOne_action
    (h : Hypercubic4) :
    ourThirdIBPAxisPlanePairOrbitMultiplicity
      (ourBianchiRotateOneOrbit.hypercubicAct h) =
      (ourThirdIBPAxisPlanePairMultiplicity
        (ourBianchiRotateOneLabeled.hypercubicAct h) : ℚ) := by
  simp [ourThirdIBPAxisPlanePairOrbitMultiplicity, ourBianchiRotateOneOrbit]

theorem ourThirdIBPAxisPlanePairOrbitMultiplicity_ourBianchiRotateTwo_action
    (h : Hypercubic4) :
    ourThirdIBPAxisPlanePairOrbitMultiplicity
      (ourBianchiRotateTwoOrbit.hypercubicAct h) =
      (ourThirdIBPAxisPlanePairMultiplicity
        (ourBianchiRotateTwoLabeled.hypercubicAct h) : ℚ) := by
  simp [ourThirdIBPAxisPlanePairOrbitMultiplicity, ourBianchiRotateTwoOrbit]

/-- The third raw coordinate vanishes after Reynolds averaging each Bianchi
summand. -/
theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourBianchiBase :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiBaseOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourBianchiBaseOrbit (1 : ℚ))) =
        ourBianchiBaseLabeled.tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            (ourBianchiBaseLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single,
      ourThirdIBPAxisPlanePairOrbitMultiplicity_ourBianchiBase_action]
    simp [ourBianchiBaseOrbit]
  simp_rw [hterm]
  rw [ourBianchiBase_signedThirdPlanePairWeight]
  norm_num

theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourBianchiRotateOne :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateOneOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourBianchiRotateOneOrbit (1 : ℚ))) =
        ourBianchiRotateOneLabeled.tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            (ourBianchiRotateOneLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single,
      ourThirdIBPAxisPlanePairOrbitMultiplicity_ourBianchiRotateOne_action]
    simp [ourBianchiRotateOneOrbit]
  simp_rw [hterm]
  rw [ourBianchiRotateOne_signedThirdPlanePairWeight]
  norm_num

theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourBianchiRotateTwo :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateTwoOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourBianchiRotateTwoOrbit (1 : ℚ))) =
        ourBianchiRotateTwoLabeled.tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            (ourBianchiRotateTwoLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single,
      ourThirdIBPAxisPlanePairOrbitMultiplicity_ourBianchiRotateTwo_action]
    simp [ourBianchiRotateTwoOrbit]
  simp_rw [hterm]
  rw [ourBianchiRotateTwo_signedThirdPlanePairWeight]
  norm_num

theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourBianchiRotateOne_neg :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateOneOrbit (-1 : ℚ))) = 0 := by
  rw [show Finsupp.single ourBianchiRotateOneOrbit (-1 : ℚ) =
      -Finsupp.single ourBianchiRotateOneOrbit (1 : ℚ) by simp,
    map_neg, map_neg,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourBianchiRotateOne]
  simp

/-- The third invariant coordinate vanishes on the complete concrete Bianchi
row under either relation policy. -/
theorem ourInvariantThirdIBPAxisCoordinate_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantThirdIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  unfold ourInvariantThirdIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourBianchi]
  simp only [LinearMap.map_add,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourBianchiBase,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourBianchiRotateOne_neg,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourBianchiRotateTwo]
  norm_num

/-- The three-coordinate correction retains the explicit Bianchi check. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  unfold ourThreeCoordinateInvariantTraceOrderCorrection
    ourThirdInvariantTraceContribution
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourTwoCoordinateInvariantTraceOrderCorrection_ourBianchi_zero,
    ourInvariantThirdIBPAxisCoordinate_ourBianchi_zero]
  simp

/- The following four bounded certificates check the new third coordinate on
the contracted-index EOM terms.  The diagonal term is zero after exact
normalization, but its raw signed sum is recorded as well. -/
set_option maxRecDepth 100000 in
theorem ourEOMZero_signedThirdPlanePairWeight :
    (∑ h : Hypercubic4,
      ourEOMZeroLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourEOMZeroLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourEOMOne_signedThirdPlanePairWeight :
    (∑ h : Hypercubic4,
      ourEOMOneLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourEOMOneLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourEOMTwo_signedThirdPlanePairWeight :
    (∑ h : Hypercubic4,
      ourEOMTwoLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourEOMTwoLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourEOMThree_signedThirdPlanePairWeight :
    (∑ h : Hypercubic4,
      ourEOMThreeLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourEOMThreeLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

theorem ourThirdIBPAxisPlanePairOrbitMultiplicity_ourEOMZero_action
    (h : Hypercubic4) :
    ourThirdIBPAxisPlanePairOrbitMultiplicity
      (ourEOMZeroOrbit.hypercubicAct h) =
      (ourThirdIBPAxisPlanePairMultiplicity
        (ourEOMZeroLabeled.hypercubicAct h) : ℚ) := by
  simp [ourThirdIBPAxisPlanePairOrbitMultiplicity, ourEOMZeroOrbit]

theorem ourThirdIBPAxisPlanePairOrbitMultiplicity_ourEOMOne_action
    (h : Hypercubic4) :
    ourThirdIBPAxisPlanePairOrbitMultiplicity
      (ourEOMOneOrbit.hypercubicAct h) =
      (ourThirdIBPAxisPlanePairMultiplicity
        (ourEOMOneLabeled.hypercubicAct h) : ℚ) := by
  simp [ourThirdIBPAxisPlanePairOrbitMultiplicity, ourEOMOneOrbit]

theorem ourThirdIBPAxisPlanePairOrbitMultiplicity_ourEOMTwo_action
    (h : Hypercubic4) :
    ourThirdIBPAxisPlanePairOrbitMultiplicity
      (ourEOMTwoOrbit.hypercubicAct h) =
      (ourThirdIBPAxisPlanePairMultiplicity
        (ourEOMTwoLabeled.hypercubicAct h) : ℚ) := by
  simp [ourThirdIBPAxisPlanePairOrbitMultiplicity, ourEOMTwoOrbit]

theorem ourThirdIBPAxisPlanePairOrbitMultiplicity_ourEOMThree_action
    (h : Hypercubic4) :
    ourThirdIBPAxisPlanePairOrbitMultiplicity
      (ourEOMThreeOrbit.hypercubicAct h) =
      (ourThirdIBPAxisPlanePairMultiplicity
        (ourEOMThreeLabeled.hypercubicAct h) : ℚ) := by
  simp [ourThirdIBPAxisPlanePairOrbitMultiplicity, ourEOMThreeOrbit]

/-- The third raw coordinate vanishes after Reynolds averaging every EOM
summand. -/
theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourEOMZero :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMZeroOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourEOMZeroOrbit (1 : ℚ))) =
        ourEOMZeroLabeled.tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            (ourEOMZeroLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single,
      ourThirdIBPAxisPlanePairOrbitMultiplicity_ourEOMZero_action]
    simp [ourEOMZeroOrbit]
  simp_rw [hterm]
  rw [ourEOMZero_signedThirdPlanePairWeight]
  norm_num

theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourEOMOne :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMOneOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourEOMOneOrbit (1 : ℚ))) =
        ourEOMOneLabeled.tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            (ourEOMOneLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single,
      ourThirdIBPAxisPlanePairOrbitMultiplicity_ourEOMOne_action]
    simp [ourEOMOneOrbit]
  simp_rw [hterm]
  rw [ourEOMOne_signedThirdPlanePairWeight]
  norm_num

theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourEOMTwo :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMTwoOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourEOMTwoOrbit (1 : ℚ))) =
        ourEOMTwoLabeled.tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            (ourEOMTwoLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single,
      ourThirdIBPAxisPlanePairOrbitMultiplicity_ourEOMTwo_action]
    simp [ourEOMTwoOrbit]
  simp_rw [hterm]
  rw [ourEOMTwo_signedThirdPlanePairWeight]
  norm_num

theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourEOMThree :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMThreeOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourEOMThreeOrbit (1 : ℚ))) =
        ourEOMThreeLabeled.tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            (ourEOMThreeLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single,
      ourThirdIBPAxisPlanePairOrbitMultiplicity_ourEOMThree_action]
    simp [ourEOMThreeOrbit]
  simp_rw [hterm]
  rw [ourEOMThree_signedThirdPlanePairWeight]
  norm_num

theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourEOMThree_neg :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMThreeOrbit (-1 : ℚ))) = 0 := by
  rw [show Finsupp.single ourEOMThreeOrbit (-1 : ℚ) =
      -Finsupp.single ourEOMThreeOrbit (1 : ℚ) by simp,
    map_neg, map_neg,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourEOMThree]
  simp

/-- The third invariant coordinate vanishes on the complete on-shell EOM
row. -/
theorem ourInvariantThirdIBPAxisCoordinate_ourEOM_zero :
    ourInvariantThirdIBPAxisCoordinate
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  unfold ourInvariantThirdIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourEOM]
  simp only [LinearMap.map_add,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourEOMZero,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourEOMOne,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourEOMThree_neg]
  norm_num

/-- The three-coordinate correction retains the explicit on-shell EOM
check. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_ourEOM_zero :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  unfold ourThreeCoordinateInvariantTraceOrderCorrection
    ourThirdInvariantTraceContribution
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourTwoCoordinateInvariantTraceOrderCorrection_ourEOM_zero,
    ourInvariantThirdIBPAxisCoordinate_ourEOM_zero]
  simp

/-- The third trace contribution is unchanged by signed hypercubic action. -/
theorem ourThirdInvariantTraceContribution_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourThirdInvariantTraceContribution
      (signedExactFieldRelabelOrbitAction h value) =
      ourThirdInvariantTraceContribution value := by
  unfold ourThirdInvariantTraceContribution
  simp only [LinearMap.smulRight_apply, LinearMap.smul_apply,
    ourInvariantThirdIBPAxisCoordinate_signed_action]

/-- OUR three-coordinate correction is unchanged by signed hypercubic
action. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (signedExactFieldRelabelOrbitAction h value) =
      ourThreeCoordinateInvariantTraceOrderCorrection value := by
  change ourTwoCoordinateInvariantTraceOrderCorrection
      (signedExactFieldRelabelOrbitAction h value) -
      ourThirdInvariantTraceContribution
        (signedExactFieldRelabelOrbitAction h value) =
      ourTwoCoordinateInvariantTraceOrderCorrection value -
        ourThirdInvariantTraceContribution value
  rw [ourTwoCoordinateInvariantTraceOrderCorrection_signed_action,
    ourThirdInvariantTraceContribution_signed_action]

/-- OUR three-coordinate correction is unchanged by full exact-carrier
Reynolds averaging. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds
    (value : ExactFieldRelabelOrbitSpace) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (exactFieldOrbitReynolds value) =
      ourThreeCoordinateInvariantTraceOrderCorrection value := by
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  simp_rw [ourThreeCoordinateInvariantTraceOrderCorrection_signed_action]
  rw [Finset.sum_const, Finset.card_univ, Hypercubic4.card_hypercubic4]
  module

/-- OUR signed-Reynolds invariant member represented by the second explicit
IBP row. -/
def ourInvariantSecondIBPRow (policy : PhysicalRelationPolicy) :
    exactFieldOrbitInvariantSubmodule :=
  ⟨exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)),
    exactFieldOrbitReynolds_invariant _⟩

/-- The averaged second IBP row belongs to the honest coordinate-free joint
invariant relation submodule under either policy. -/
theorem ourInvariantSecondIBPRow_mem (policy : PhysicalRelationPolicy) :
    ourInvariantSecondIBPRow policy ∈ jointInvariantRelationSubmodule policy := by
  rw [mem_jointInvariantRelationSubmodule_iff]
  change exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) ∈
      orbitPhysicalRelationSubmodule policy
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  apply (orbitPhysicalRelationSubmodule policy).smul_mem
  apply Submodule.sum_mem
  intro h _
  apply orbitPhysicalRelationSubmodule_signed_invariant policy h
  exact ⟨Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1, rfl⟩

/-- The three-coordinate correction annihilates the actual invariant second
IBP member, not merely its unaveraged presentation. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_invariantSecondIBP_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (ourInvariantSecondIBPRow policy).1 = 0 := by
  rw [show (ourInvariantSecondIBPRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) by rfl,
    ourThreeCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourSecondIBP_zero]

/-- The three-coordinate correction retains the actual invariant commutator
member for either policy. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_invariantCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (ourInvariantCommutatorRow policy).1 = 0 := by
  rw [show (ourInvariantCommutatorRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) by rfl,
    ourThreeCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourCommutator_zero]

/-- The three-coordinate correction retains the actual invariant first-IBP
member. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_invariantIBP_zero :
    ourThreeCoordinateInvariantTraceOrderCorrection ourInvariantIBPRow.1 = 0 := by
  rw [show ourInvariantIBPRow.1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator .offShell
          (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) by rfl,
    ourThreeCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourIBP_zero]

/-- The three-coordinate correction retains the actual invariant Bianchi
member under either policy. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_invariantBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (ourInvariantBianchiRow policy).1 = 0 := by
  rw [show (ourInvariantBianchiRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) by rfl,
    ourThreeCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourBianchi_zero]

/-- The three-coordinate correction retains the actual invariant on-shell
EOM member. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_invariantEOM_zero :
    ourThreeCoordinateInvariantTraceOrderCorrection ourInvariantEOMRow.1 = 0 := by
  rw [show ourInvariantEOMRow.1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator .onShell
          (Finsupp.single ourFieldSevenEOMGenerator 1)) by rfl,
    ourThreeCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourEOM_zero]

#print axioms ourSecondIBPSignedAxisWeight
#print axioms ourSecondIBPOldPlanePairSignedWeight
#print axioms ourSecondIBPThirdPlanePairSignedWeight
#print axioms ourTwoCoordinateInvariantTraceOrderCorrection_ourSecondIBP_ne_zero
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_ourSecondIBP_zero
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_ourCommutator_zero
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_ourIBP_zero
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_liftedTraceGenerator_zero
#print axioms ourBianchiBase_signedThirdPlanePairWeight
#print axioms ourBianchiRotateOne_signedThirdPlanePairWeight
#print axioms ourBianchiRotateTwo_signedThirdPlanePairWeight
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_ourBianchi_zero
#print axioms ourEOMZero_signedThirdPlanePairWeight
#print axioms ourEOMOne_signedThirdPlanePairWeight
#print axioms ourEOMTwo_signedThirdPlanePairWeight
#print axioms ourEOMThree_signedThirdPlanePairWeight
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_ourEOM_zero
#print axioms ourInvariantSecondIBPRow_mem
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_invariantSecondIBP_zero
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_invariantCommutator_zero
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_invariantIBP_zero
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_invariantBianchi_zero
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_invariantEOM_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
