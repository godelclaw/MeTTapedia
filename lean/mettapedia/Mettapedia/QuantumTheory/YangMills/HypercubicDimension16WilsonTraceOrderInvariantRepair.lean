import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderRepair
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceInvariantWitness
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldEightTracePhysicalLift
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16JointPhysicalQuotient

/-!
# OUR signed-hypercubic trace-order repair

The local trace-order repair records a forced seven-field compensator for
one covariant-commutator row.  This module constructs and tests two
field-relabel-invariant coordinates averaged over the signed hypercubic
action, then compares their prescribed combination with the canonical
field-eight trace coordinate.  The first coordinate exposes a concrete IBP
obstruction; the second supplies the exact independent value that repairs
that row.  The construction below is an OUR finite-coordinate interface.  It
does not claim that the resulting coordinate annihilates the complete
physical relation submodule; that remaining extension test is the point of
the construction.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantRepair

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
open HypercubicDimension16IBPTraceRelations
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16IncomingCommutatorTraceInvariantWitness
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceProjection
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16FieldEightTracePhysicalLift

/-- OUR field-relabel-invariant derivative-axis multiplicity, evaluated on a
seven-field relabel orbit. -/
def derivativeAxisOrbitMultiplicity (word : List (Fin 4)) :
    FieldSevenOrbitCarrier → ℚ :=
  Quotient.lift (fun sector =>
    (derivativeAxisWordMultiplicity word sector : ℚ)) (by
      intro left right horbit
      change MulAction.orbitRel (Equiv.Perm (Fin 7))
        (LabeledLocalWordSector 7 2) left right at horbit
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at horbit
      rcases horbit with ⟨rename, hrename⟩
      change LabeledLocalWordSector.relabel rename right = left at hrename
      rw [← hrename]
      exact_mod_cast derivativeAxisWordMultiplicity_relabel word rename right)

/-- OUR linear derivative-axis coordinate on the seven-field orbit space. -/
def ourDerivativeAxisCoordinate (word : List (Fin 4)) :
    FieldSevenOrbitSpace →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ (derivativeAxisOrbitMultiplicity word)

@[simp] theorem ourDerivativeAxisCoordinate_single
    (word : List (Fin 4)) (target : FieldSevenOrbitCarrier) (coefficient : ℚ) :
    ourDerivativeAxisCoordinate word (Finsupp.single target coefficient) =
      coefficient * derivativeAxisOrbitMultiplicity word target := by
  simp [ourDerivativeAxisCoordinate]

/-- The derivative-axis coordinate at the source orbit is one. -/
theorem derivativeAxisOrbitMultiplicity_source :
    derivativeAxisOrbitMultiplicity [0, 2] sourceSevenOrbit = 1 := by
  change (derivativeAxisWordMultiplicity [0, 2] sourceLabeled : ℚ) = 1
  norm_num [sourceAxisMultiplicity]

/-- The derivative-axis coordinate at the swapped orbit is zero. -/
theorem derivativeAxisOrbitMultiplicity_swapped :
    derivativeAxisOrbitMultiplicity [0, 2] swappedSevenOrbit = 0 := by
  change (derivativeAxisWordMultiplicity [0, 2] swappedLabeled : ℚ) = 0
  norm_num [swappedAxisMultiplicity]

set_option maxRecDepth 100000 in
/-- The signed source orbit has total derivative-axis weight `32` over
the hypercubic group.  This is a bounded kernel-reduced finite calculation. -/
theorem source_signedAxisWeight :
    (∑ h : Hypercubic4,
      sourceLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (sourceLabeled.hypercubicAct h) : ℚ)) = 32 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The signed swapped orbit has total derivative-axis weight `-32` over
the hypercubic group.  This is a bounded kernel-reduced finite calculation. -/
theorem swapped_signedAxisWeight :
    (∑ h : Hypercubic4,
      swappedLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (swappedLabeled.hypercubicAct h) : ℚ)) = -32 := by
  decide +kernel

/-- OUR exact seven-field component of a full orbit-carrier vector. -/
def exactFieldSevenProjection : ExactFieldRelabelOrbitSpace →ₗ[ℚ]
    FieldSevenOrbitSpace :=
  (LinearMap.fst ℚ FieldSevenOrbitSpace FieldEightOrbitSpace).comp
    exactFieldSevenEightProjection

/-- The dependent seven-field cast commutes with the hypercubic action. -/
theorem exactFieldSevenOrbitCast_hypercubicAct
    (h : Hypercubic4) (fieldCount : Fin 9)
    (hfield : fieldCount = ourSevenFieldCount)
    (orbit : FieldRelabelOrbitCarrier fieldCount.1
      (dimension16DerivativeCount fieldCount)) :
    exactFieldSevenOrbitCast fieldCount hfield (orbit.hypercubicAct h) =
      (exactFieldSevenOrbitCast fieldCount hfield orbit).hypercubicAct h := by
  subst fieldCount
  rfl

/-- The dependent seven-field cast preserves the hypercubic tensor sign. -/
theorem exactFieldSevenOrbitCast_tensorSign
    (h : Hypercubic4) (fieldCount : Fin 9)
    (hfield : fieldCount = ourSevenFieldCount)
    (orbit : FieldRelabelOrbitCarrier fieldCount.1
      (dimension16DerivativeCount fieldCount)) :
    (exactFieldSevenOrbitCast fieldCount hfield orbit).tensorSign h =
      orbit.tensorSign h := by
  subst fieldCount
  rfl

/-- OUR exact seven-field projection intertwines the signed hypercubic
actions. -/
theorem exactFieldSevenProjection_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    exactFieldSevenProjection (signedExactFieldRelabelOrbitAction h value) =
      signedSectorFieldOrbitAction h 7 2 (exactFieldSevenProjection value) := by
  induction value using Finsupp.induction_linear with
  | zero => simp [exactFieldSevenProjection]
  | add left right hleft hright =>
      simp [hleft, hright]
  | single target coefficient =>
      rcases target with ⟨fieldCount, orbit⟩
      by_cases hfield : fieldCount = ourSevenFieldCount
      · subst fieldCount
        simp [exactFieldSevenProjection, exactFieldSevenEightProjection,
          exactFieldSevenEightProjectionBasis,
          signedExactFieldRelabelOrbitAction_single,
          exactFieldRelabelOrbitAct, exactFieldRelabelOrbitTensorSign,
          signedSectorFieldOrbitAction_single,
          ourSevenFieldCount]
        apply congrArg (fun target : FieldSevenOrbitCarrier =>
          Finsupp.single target (coefficient * orbit.tensorSign h))
        exact exactFieldSevenOrbitCast_hypercubicAct h _ rfl orbit
      · by_cases height : fieldCount = ourEightFieldCount
        · subst fieldCount
          have hEightSeven : ourEightFieldCount ≠ ourSevenFieldCount := by
            decide
          simp [exactFieldSevenProjection, exactFieldSevenEightProjection,
            exactFieldSevenEightProjectionBasis,
            signedExactFieldRelabelOrbitAction_single,
            exactFieldRelabelOrbitAct, exactFieldRelabelOrbitTensorSign,
            hEightSeven]
        · simp [exactFieldSevenProjection, exactFieldSevenEightProjection,
            exactFieldSevenEightProjectionBasis,
            signedExactFieldRelabelOrbitAction_single,
            exactFieldRelabelOrbitAct, exactFieldRelabelOrbitTensorSign,
            hfield, height]

/-- OUR seven-field projection commutes with full-carrier Reynolds averaging. -/
theorem exactFieldSevenProjection_exactFieldOrbitReynolds
    (value : ExactFieldRelabelOrbitSpace) :
    exactFieldSevenProjection (exactFieldOrbitReynolds value) =
      sectorFieldOrbitReynolds 7 2 (exactFieldSevenProjection value) := by
  unfold exactFieldOrbitReynolds sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  simp_rw [exactFieldSevenProjection_signed_action]

/-- The derivative-axis orbit coordinate follows the source under a signed
hypercubic action. -/
theorem derivativeAxisOrbitMultiplicity_source_action (h : Hypercubic4) :
    derivativeAxisOrbitMultiplicity [0, 2]
      (sourceSevenOrbit.hypercubicAct h) =
      (derivativeAxisWordMultiplicity [0, 2]
        (sourceLabeled.hypercubicAct h) : ℚ) := by
  simp [derivativeAxisOrbitMultiplicity, sourceSevenOrbit]

/-- The derivative-axis orbit coordinate follows the swapped source under a
signed hypercubic action. -/
theorem derivativeAxisOrbitMultiplicity_swapped_action (h : Hypercubic4) :
    derivativeAxisOrbitMultiplicity [0, 2]
      (swappedSevenOrbit.hypercubicAct h) =
      (derivativeAxisWordMultiplicity [0, 2]
        (swappedLabeled.hypercubicAct h) : ℚ) := by
  simp [derivativeAxisOrbitMultiplicity, swappedSevenOrbit]

/-- OUR derivative-axis coordinate of the Reynolds average of the source
orbit is exactly `1 / 12`. -/
theorem derivativeAxisCoordinate_reynolds_source :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single sourceSevenOrbit (1 : ℚ))) = 1 / 12 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single sourceSevenOrbit (1 : ℚ))) =
        sourceLabeled.tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            (sourceLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single,
      derivativeAxisOrbitMultiplicity_source_action]
    simp [sourceSevenOrbit]
  simp_rw [hterm]
  rw [source_signedAxisWeight]
  norm_num

/-- OUR derivative-axis coordinate of the Reynolds average of the swapped
orbit is exactly `-1 / 12`. -/
theorem derivativeAxisCoordinate_reynolds_swapped :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single swappedSevenOrbit (1 : ℚ))) = -(1 / 12) := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single swappedSevenOrbit (1 : ℚ))) =
        swappedLabeled.tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            (swappedLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single,
      derivativeAxisOrbitMultiplicity_swapped_action]
    simp [swappedSevenOrbit]
  simp_rw [hterm]
  rw [swapped_signedAxisWeight]
  norm_num

/-- On the full seven-field component of OUR coupled commutator, Reynolds
averaging leaves the exact scalar `1 / 6`. -/
theorem derivativeAxisCoordinate_reynolds_coupledIncoming_fst :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2 coupledIncomingCommutatorVector.1) =
      1 / 6 := by
  rw [coupledIncomingCommutatorVector_fst, LinearMap.map_sub,
    LinearMap.map_sub,
    derivativeAxisCoordinate_reynolds_source,
    derivativeAxisCoordinate_reynolds_swapped]
  norm_num

/-- OUR scaled signed-hypercubic-invariant seven-field coordinate on the
full exact carrier.  The scale `6` is forced by the finite orbit calculation
above. -/
def ourInvariantSevenAxisCoordinate : ExactFieldRelabelOrbitSpace →ₗ[ℚ] ℚ :=
  (6 : ℚ) •
    ((ourDerivativeAxisCoordinate [0, 2]).comp
      (exactFieldSevenProjection.comp exactFieldOrbitReynolds))

/-- OUR scaled seven-field coordinate is unchanged by every signed
hypercubic action. -/
theorem ourInvariantSevenAxisCoordinate_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourInvariantSevenAxisCoordinate
      (signedExactFieldRelabelOrbitAction h value) =
      ourInvariantSevenAxisCoordinate value := by
  unfold ourInvariantSevenAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldOrbitReynolds_action]

/-- The exact seven-field projection of OUR full physical commutator is the
first component of the coupled commutator row. -/
theorem exactFieldSevenProjection_ourCommutator_full
    (policy : PhysicalRelationPolicy) :
    exactFieldSevenProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) =
      coupledIncomingCommutatorVector.1 := by
  change (exactFieldSevenEightProjection
    (orbitPhysicalRelationOperator policy
      (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1))).1 = _
  rw [exactFieldSevenEightProjection_ourCommutator_full]

/-- OUR invariant seven-field coordinate evaluates the full physical
commutator to one, for either relation policy. -/
theorem ourInvariantSevenAxisCoordinate_ourCommutator
    (policy : PhysicalRelationPolicy) :
    ourInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 1 := by
  unfold ourInvariantSevenAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourCommutator_full,
    derivativeAxisCoordinate_reynolds_coupledIncoming_fst]
  norm_num

/-- OUR signed-hypercubic-invariant seven-field compensator, valued in the
certified eight-field trace quotient. -/
def ourInvariantSevenTraceCompensator :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ourInvariantSevenAxisCoordinate.smulRight literalIncomingCommutatorClass

/-- OUR invariant seven-field compensator is unchanged by every signed
hypercubic action. -/
theorem ourInvariantSevenTraceCompensator_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourInvariantSevenTraceCompensator
      (signedExactFieldRelabelOrbitAction h value) =
      ourInvariantSevenTraceCompensator value := by
  simp only [ourInvariantSevenTraceCompensator, LinearMap.smulRight_apply,
    ourInvariantSevenAxisCoordinate_signed_action]

/-- OUR invariant seven-field compensator recovers the forced literal trace
class on the full physical commutator. -/
theorem ourInvariantSevenTraceCompensator_ourCommutator
    (policy : PhysicalRelationPolicy) :
    ourInvariantSevenTraceCompensator
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) =
      literalIncomingCommutatorClass := by
  simp only [ourInvariantSevenTraceCompensator, LinearMap.smulRight_apply,
    ourInvariantSevenAxisCoordinate_ourCommutator]
  simp

/-- OUR full trace-order correction: the signed-hypercubic seven-field
compensator minus the canonical eight-field trace coordinate. -/
def ourInvariantTraceOrderCorrection :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ourInvariantSevenTraceCompensator - exactFieldEightTraceProjection

/-- OUR full trace-order correction is unchanged by every signed hypercubic
action. -/
theorem ourInvariantTraceOrderCorrection_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourInvariantTraceOrderCorrection
      (signedExactFieldRelabelOrbitAction h value) =
      ourInvariantTraceOrderCorrection value := by
  unfold ourInvariantTraceOrderCorrection
  change ourInvariantSevenTraceCompensator
      (signedExactFieldRelabelOrbitAction h value) -
      exactFieldEightTraceProjection
        (signedExactFieldRelabelOrbitAction h value) =
      ourInvariantSevenTraceCompensator value -
        exactFieldEightTraceProjection value
  rw [ourInvariantSevenTraceCompensator_signed_action,
    exactFieldEightTraceProjection_signed_action]

/-- OUR full signed-hypercubic correction annihilates the complete concrete
covariant-commutator column, for either relation policy. -/
theorem ourInvariantTraceOrderCorrection_ourCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  change ourInvariantSevenTraceCompensator
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) -
      exactFieldEightTraceProjection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0
  rw [ourInvariantSevenTraceCompensator_ourCommutator,
    exactFieldEightTraceProjection_ourCommutator]
  abel

/-- OUR invariant correction is unchanged by full-carrier Reynolds
averaging. -/
theorem ourInvariantTraceOrderCorrection_exactFieldOrbitReynolds
    (value : ExactFieldRelabelOrbitSpace) :
    ourInvariantTraceOrderCorrection (exactFieldOrbitReynolds value) =
      ourInvariantTraceOrderCorrection value := by
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  simp_rw [ourInvariantTraceOrderCorrection_signed_action]
  rw [Finset.sum_const, Finset.card_univ, Hypercubic4.card_hypercubic4]
  module

/-- The new correction also annihilates the actual signed-hypercubic
invariant commutator relation inside the coordinate-free joint relation
space. -/
theorem ourInvariantTraceOrderCorrection_invariantCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantTraceOrderCorrection (ourInvariantCommutatorRow policy).1 =
      0 := by
  rw [show (ourInvariantCommutatorRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) by rfl,
    ourInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourInvariantTraceOrderCorrection_ourCommutator_zero]

/-- OUR seven-field projection vanishes on the typed derivative-free
eight-field inclusion. -/
theorem exactFieldSevenProjection_fieldEightExactEmbed
    (value : FieldEightOrbitSpace) :
    exactFieldSevenProjection (fieldEightExactEmbed value) = 0 := by
  induction value using Finsupp.induction_linear with
  | zero => simp [exactFieldSevenProjection, fieldEightExactEmbed]
  | add left right hleft hright =>
      simp [hleft, hright]
  | single target coefficient =>
      rw [fieldEightExactEmbed_single]
      change (exactFieldSevenEightProjection
        (Finsupp.single (fieldEightExactCarrier target) coefficient)).1 = 0
      rw [exactFieldSevenEightProjection_single]
      simp [
        exactFieldSevenEightProjectionBasis, ourSevenFieldCount,
        ourEightFieldCount, fieldEightExactCarrier]

/-- OUR invariant seven-field axis coordinate vanishes on every typed
derivative-free eight-field inclusion. -/
theorem ourInvariantSevenAxisCoordinate_fieldEightExactEmbed_zero
    (value : FieldEightOrbitSpace) :
    ourInvariantSevenAxisCoordinate (fieldEightExactEmbed value) = 0 := by
  unfold ourInvariantSevenAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_fieldEightExactEmbed]
  simp

/-- OUR invariant seven-field trace compensator vanishes on every typed
derivative-free eight-field inclusion. -/
theorem ourInvariantSevenTraceCompensator_fieldEightExactEmbed_zero
    (value : FieldEightOrbitSpace) :
    ourInvariantSevenTraceCompensator (fieldEightExactEmbed value) = 0 := by
  simp only [ourInvariantSevenTraceCompensator, LinearMap.smulRight_apply,
    ourInvariantSevenAxisCoordinate_fieldEightExactEmbed_zero, zero_smul]

/-- A derivative-free eight-field physical trace row has zero canonical
trace class in OUR quotient. -/
theorem ourExactFieldEightTraceClassMap_fieldEightPhysicalTraceRow_zero
    (generator : FieldEightTraceGenerator) :
    exactFieldEightTraceClassMap (fieldEightPhysicalTraceRow generator) = 0 := by
  change (Submodule.mkQ fieldEightPhysicalTraceRelationSubmodule)
      (fieldEightCoinvariantTraceRow generator) = 0
  apply (Submodule.Quotient.mk_eq_zero
    fieldEightPhysicalTraceRelationSubmodule).mpr
  exact Submodule.subset_span ⟨generator, rfl⟩

/-- OUR invariant trace-order correction annihilates every typed
derivative-free eight-field trace row. -/
theorem ourInvariantTraceOrderCorrection_fieldEightTraceRow_zero
    (generator : FieldEightTraceGenerator) :
    ourInvariantTraceOrderCorrection
      (fieldEightExactEmbed (fieldEightPhysicalTraceRow generator)) = 0 := by
  change ourInvariantSevenTraceCompensator
      (fieldEightExactEmbed (fieldEightPhysicalTraceRow generator)) -
      exactFieldEightTraceProjection
        (fieldEightExactEmbed (fieldEightPhysicalTraceRow generator)) = 0
  rw [ourInvariantSevenTraceCompensator_fieldEightExactEmbed_zero]
  change 0 - exactFieldEightTraceClassMap
      (exactFieldEightProjection
        (fieldEightExactEmbed (fieldEightPhysicalTraceRow generator))) = 0
  rw [exactFieldEightProjection_fieldEightExactEmbed,
    ourExactFieldEightTraceClassMap_fieldEightPhysicalTraceRow_zero]
  simp

/-- OUR invariant trace-order correction annihilates the actual full-carrier
lift of every derivative-free eight-field physical trace generator, for both
relation policies. -/
theorem ourInvariantTraceOrderCorrection_liftedTraceGenerator_zero
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)) =
      0 := by
  rw [ourOrbitPhysicalRelationOperator_lift]
  exact ourInvariantTraceOrderCorrection_fieldEightTraceRow_zero generator

/-- The same correction annihilates the signed-hypercubic Reynolds average
of every lifted derivative-free eight-field physical trace row. -/
theorem ourInvariantTraceOrderCorrection_invariantLiftedTraceGenerator_zero
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourInvariantTraceOrderCorrection
      (exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1))) =
      0 := by
  rw [ourInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourInvariantTraceOrderCorrection_liftedTraceGenerator_zero]

/-- OUR outermost derivative position for an explicit seven-field IBP row. -/
abbrev ourIBPPosition :
    Fin (dimension16DerivativeCount ourFieldSevenCommutatorCarrier.1) :=
  ⟨0, by norm_num [ourFieldSevenCommutatorCarrier,
    dimension16DerivativeCount]⟩

/-- OUR labeled summand obtained by moving that outermost derivative to one
field of the explicit seven-field carrier. -/
abbrev ourIBPLabeledTerm (field : Fin 7) :
    LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData
      (setDerivativeOwner ourFieldSevenCommutatorCarrier ourIBPPosition field).2)

/-- OUR ordinary field-relabel orbit of one explicit IBP summand. -/
abbrev ourIBPOrbit (field : Fin 7) : FieldSevenOrbitCarrier :=
  Quotient.mk _ (ourIBPLabeledTerm field)

/-- OUR exact full-carrier target of one explicit seven-field IBP summand. -/
abbrev ourIBPExactTarget (field : Fin 7) : ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourIBPOrbit field⟩

/-- OUR genuine physical integration-by-parts generator used to test the
candidate signed-hypercubic correction. -/
def ourFieldSevenIBPGenerator
    (policy : PhysicalRelationPolicy) : PhysicalRelationGenerator policy :=
  .integrationByParts ourFieldSevenCommutatorCarrier ourIBPPosition (by
    intro other
    change 0 ≤ other.1
    omega)

/- This bounded finite calculation is replayed by `decide +kernel`; it is
the coefficient computation for the explicit IBP extension test. -/
set_option maxRecDepth 100000 in
theorem ourIBPSignedAxisWeight (field : Fin 7) :
  ∑ h : Hypercubic4,
    (ourIBPLabeledTerm field).tensorSign h *
      (derivativeAxisWordMultiplicity [0, 2]
        ((ourIBPLabeledTerm field).hypercubicAct h) : ℚ) =
    if field = 0 then 32 else 0 := by
  fin_cases field <;> decide +kernel

/-- The derivative-axis orbit coordinate follows each explicit IBP summand
under the signed hypercubic action. -/
theorem derivativeAxisOrbitMultiplicity_ourIBP_action
    (field : Fin 7) (h : Hypercubic4) :
    derivativeAxisOrbitMultiplicity [0, 2]
      ((ourIBPOrbit field).hypercubicAct h) =
      (derivativeAxisWordMultiplicity [0, 2]
        ((ourIBPLabeledTerm field).hypercubicAct h) : ℚ) := by
  simp [derivativeAxisOrbitMultiplicity, ourIBPOrbit]

/-- The Reynolds-averaged derivative-axis coordinate of each explicit IBP
summand is `1 / 12` at field zero and zero at the other six fields. -/
theorem derivativeAxisCoordinate_reynolds_ourIBP
    (field : Fin 7) :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (ourIBPOrbit field) (1 : ℚ))) =
      if field = 0 then 1 / 12 else 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (ourIBPOrbit field) (1 : ℚ))) =
        (ourIBPLabeledTerm field).tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            ((ourIBPLabeledTerm field).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single,
      derivativeAxisOrbitMultiplicity_ourIBP_action]
    simp [ourIBPOrbit]
  simp_rw [hterm]
  rw [ourIBPSignedAxisWeight]
  split_ifs <;> norm_num

/-- The exact seven-field projection of one explicit IBP target is its
corresponding ordinary seven-field orbit basis vector. -/
theorem exactFieldSevenProjection_ourIBPExactTarget_single
    (field : Fin 7) (coefficient : ℚ) :
    exactFieldSevenProjection
      (Finsupp.single (ourIBPExactTarget field) coefficient) =
      Finsupp.single (ourIBPOrbit field) coefficient := by
  change (exactFieldSevenEightProjection
    (Finsupp.single (ourIBPExactTarget field) coefficient)).1 = _
  rw [exactFieldSevenEightProjection_single]
  simp [exactFieldSevenEightProjectionBasis,
    exactFieldSevenOrbitCast_self]

/-- The signed-hypercubic seven-field coordinate of one explicit IBP target
is `1 / 2` at field zero and zero elsewhere. -/
theorem ourInvariantSevenAxisCoordinate_ourIBPExactTarget_single
    (field : Fin 7) :
    ourInvariantSevenAxisCoordinate
      (Finsupp.single (ourIBPExactTarget field) (1 : ℚ)) =
      if field = 0 then 1 / 2 else 0 := by
  unfold ourInvariantSevenAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourIBPExactTarget_single,
    derivativeAxisCoordinate_reynolds_ourIBP]
  split_ifs <;> norm_num

/-- The field-relabel normalization of each explicit IBP summand has the
stated exact seven-field target. -/
theorem exactFieldRelabelOrbitOfOriented_ourIBPTerm
    (field : Fin 7) :
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData
        (setDerivativeOwner ourFieldSevenCommutatorCarrier
          ourIBPPosition field)) = ourIBPExactTarget field := by
  rfl

/- This bounded finite calculation records the orientation of every explicit
IBP summand before its field-relabel normalization. -/
set_option maxRecDepth 100000 in
theorem ourIBPOrientationCoefficient (field : Fin 7) :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment
        (setDerivativeOwner ourFieldSevenCommutatorCarrier
          ourIBPPosition field).2) = 1 := by
  fin_cases field <;> decide +kernel

/-- The exact field-relabel normalization of each explicit IBP basis term is
its stated seven-field exact target with unit orientation. -/
theorem ourNormalizeExactContextualBasis_ourIBPTerm
    (field : Fin 7) :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (setDerivativeOwner ourFieldSevenCommutatorCarrier
          ourIBPPosition field)) =
      Finsupp.single (ourIBPExactTarget field) 1 := by
  unfold normalizeExactContextualBasis
  rw [LinearMap.map_smul, normalizeExactFieldRelabel_single]
  unfold normalizeExactFieldRelabelBasis
  rw [exactFieldRelabelOrbitOfOriented_ourIBPTerm,
    ourIBPOrientationCoefficient]
  simp

/-- The full physical orbit operator sends OUR explicit integration-by-parts
generator to the seven stated exact targets. -/
theorem orbitPhysicalRelationOperator_ourIBP :
    orbitPhysicalRelationOperator .offShell
      (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1) =
      ∑ field : Fin 7, Finsupp.single (ourIBPExactTarget field) 1 := by
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  simp only [one_smul, ourFieldSevenIBPGenerator, physicalRelationRow,
    integrationByPartsRow, map_sum]
  apply Finset.sum_congr rfl
  intro field _
  rw [normalizeExactContextual_single]
  simp only [one_smul]
  exact ourNormalizeExactContextualBasis_ourIBPTerm field

/-- The signed-hypercubic seven-field coordinate of OUR explicit physical
IBP row is exactly `1 / 2`. -/
theorem ourInvariantSevenAxisCoordinate_ourIBP :
    ourInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 1 / 2 := by
  rw [orbitPhysicalRelationOperator_ourIBP, map_sum]
  simp_rw [ourInvariantSevenAxisCoordinate_ourIBPExactTarget_single]
  norm_num

/-- OUR invariant seven-field trace compensator takes the explicit physical
IBP generator to one half of the certified incoming trace class. -/
theorem ourInvariantSevenTraceCompensator_ourIBP :
    ourInvariantSevenTraceCompensator
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) =
      (1 / 2 : ℚ) • literalIncomingCommutatorClass := by
  simp only [ourInvariantSevenTraceCompensator, LinearMap.smulRight_apply,
    ourInvariantSevenAxisCoordinate_ourIBP]

/-- The exact eight-field projection of OUR explicit seven-field IBP row is
zero. -/
theorem exactFieldEightProjection_ourIBP_zero :
    exactFieldEightProjection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 := by
  rw [orbitPhysicalRelationOperator_ourIBP, map_sum]
  apply Finset.sum_eq_zero
  intro field _
  change exactFieldEightProjection
    (Finsupp.single (ourIBPExactTarget field) (1 : ℚ)) = 0
  rw [exactFieldEightProjection_single]
  simp [exactFieldEightProjectionBasis,
    ourSevenFieldCount, ourEightFieldCount]

/-- The canonical eight-field trace coordinate vanishes on OUR explicit
seven-field IBP generator. -/
theorem exactFieldEightTraceProjection_ourIBP_zero :
    exactFieldEightTraceProjection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 := by
  change exactFieldEightTraceClassMap
    (exactFieldEightProjection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1))) = 0
  rw [exactFieldEightProjection_ourIBP_zero]
  exact map_zero _

/-- The candidate invariant trace-order correction has the explicit nonzero
value `1 / 2` of the incoming trace class on OUR physical IBP row.  Thus this
one-coordinate repair cannot annihilate the full off-shell relation family. -/
theorem ourInvariantTraceOrderCorrection_ourIBP :
    ourInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) =
      (1 / 2 : ℚ) • literalIncomingCommutatorClass := by
  change ourInvariantSevenTraceCompensator
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) -
      exactFieldEightTraceProjection
        (orbitPhysicalRelationOperator .offShell
          (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = _
  rw [ourInvariantSevenTraceCompensator_ourIBP,
    exactFieldEightTraceProjection_ourIBP_zero, sub_zero]

/-- The candidate invariant trace-order correction is nonzero on OUR
explicit physical IBP row. -/
theorem ourInvariantTraceOrderCorrection_ourIBP_ne_zero :
    ourInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) ≠ 0 := by
  rw [ourInvariantTraceOrderCorrection_ourIBP]
  exact smul_ne_zero (by norm_num) literalIncomingCommutatorClass_ne_zero

/-- The same failure persists after Reynolds averaging, so it is an explicit
nonzero member of the coordinate-free off-shell joint relation space. -/
theorem ourInvariantTraceOrderCorrection_reynolds_ourIBP_ne_zero :
    ourInvariantTraceOrderCorrection
      (exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator .offShell
          (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1))) ≠ 0 := by
  rw [ourInvariantTraceOrderCorrection_exactFieldOrbitReynolds]
  exact ourInvariantTraceOrderCorrection_ourIBP_ne_zero

/-- OUR multiplicity of an ordered pair of distinct fields carrying specified
oriented planes and one-letter derivative words.  The count itself is
field-relabel invariant. -/
def derivativeAxisPlanePairMultiplicity
    (firstPlane secondPlane : OrientedPlane)
    (firstAxis secondAxis : Fin 4)
    (sector : LabeledLocalWordSector 7 2) : ℕ :=
  ∑ first : Fin 7, ∑ second : Fin 7,
    if first ≠ second ∧
      (sector.decoration.1 first).plane = firstPlane ∧
      List.ofFn (sector.decoration.1 first).derivativeAxis = [firstAxis] ∧
      (sector.decoration.1 second).plane = secondPlane ∧
      List.ofFn (sector.decoration.1 second).derivativeAxis = [secondAxis]
    then 1 else 0

/-- The ordered axis-plane pair multiplicity is unaffected by a uniform
renaming of field labels. -/
theorem derivativeAxisPlanePairMultiplicity_relabel
    (firstPlane secondPlane : OrientedPlane)
    (firstAxis secondAxis : Fin 4)
    (rename : Equiv.Perm (Fin 7))
    (sector : LabeledLocalWordSector 7 2) :
    derivativeAxisPlanePairMultiplicity firstPlane secondPlane firstAxis secondAxis
      (LabeledLocalWordSector.relabel rename sector) =
      derivativeAxisPlanePairMultiplicity firstPlane secondPlane firstAxis secondAxis
        sector := by
  let indicator : Fin 7 → Fin 7 → ℕ := fun first second =>
    if first ≠ second ∧
      (sector.decoration.1 first).plane = firstPlane ∧
      List.ofFn (sector.decoration.1 first).derivativeAxis = [firstAxis] ∧
      (sector.decoration.1 second).plane = secondPlane ∧
      List.ofFn (sector.decoration.1 second).derivativeAxis = [secondAxis]
    then 1 else 0
  unfold derivativeAxisPlanePairMultiplicity
  have hterm (first second : Fin 7) :
      (if first ≠ second ∧
        ((LabeledLocalWordSector.relabel rename sector).decoration.1 first).plane =
          firstPlane ∧
        List.ofFn
            ((LabeledLocalWordSector.relabel rename sector).decoration.1 first).derivativeAxis =
          [firstAxis] ∧
        ((LabeledLocalWordSector.relabel rename sector).decoration.1 second).plane =
          secondPlane ∧
        List.ofFn
            ((LabeledLocalWordSector.relabel rename sector).decoration.1 second).derivativeAxis =
          [secondAxis]
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
          firstPlane ∧
        List.ofFn
            ((LabeledLocalWordSector.relabel rename sector).decoration.1 first).derivativeAxis =
          [firstAxis] ∧
        ((LabeledLocalWordSector.relabel rename sector).decoration.1 second).plane =
          secondPlane ∧
        List.ofFn
            ((LabeledLocalWordSector.relabel rename sector).decoration.1 second).derivativeAxis =
          [secondAxis]
      then 1 else 0) =
      ∑ first, ∑ second, indicator (rename.symm first) second := by
        apply Finset.sum_congr rfl
        intro first _
        calc
          (∑ second,
            if first ≠ second ∧
              ((LabeledLocalWordSector.relabel rename sector).decoration.1 first).plane =
                firstPlane ∧
              List.ofFn
                  ((LabeledLocalWordSector.relabel rename sector).decoration.1 first).derivativeAxis =
                [firstAxis] ∧
              ((LabeledLocalWordSector.relabel rename sector).decoration.1 second).plane =
                secondPlane ∧
              List.ofFn
                  ((LabeledLocalWordSector.relabel rename sector).decoration.1 second).derivativeAxis =
                [secondAxis]
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

/-- OUR selected split-derivative axis-plane pattern.  It is zero on the
commutator's two-derivative terms and detects the IBP distribution terms. -/
abbrev ourIBPAxisPlanePairMultiplicity :
    LabeledLocalWordSector 7 2 → ℕ :=
  derivativeAxisPlanePairMultiplicity
    (planeLookup 2 3) (planeLookup 1 3) 2 0

/-- OUR selected split-derivative pattern descends to ordinary seven-field
relabel orbits. -/
def ourIBPAxisPlanePairOrbitMultiplicity : FieldSevenOrbitCarrier → ℚ :=
  Quotient.lift (fun sector =>
    (ourIBPAxisPlanePairMultiplicity sector : ℚ)) (by
      intro left right horbit
      change MulAction.orbitRel (Equiv.Perm (Fin 7))
        (LabeledLocalWordSector 7 2) left right at horbit
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at horbit
      rcases horbit with ⟨rename, hrename⟩
      change LabeledLocalWordSector.relabel rename right = left at hrename
      rw [← hrename]
      exact_mod_cast derivativeAxisPlanePairMultiplicity_relabel
        (planeLookup 2 3) (planeLookup 1 3) 2 0 rename right)

/-- OUR linear seven-field coordinate for the selected split-derivative
axis-plane pattern. -/
def ourIBPAxisPlanePairCoordinate : FieldSevenOrbitSpace →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ ourIBPAxisPlanePairOrbitMultiplicity

@[simp] theorem ourIBPAxisPlanePairCoordinate_single
    (target : FieldSevenOrbitCarrier) (coefficient : ℚ) :
    ourIBPAxisPlanePairCoordinate (Finsupp.single target coefficient) =
      coefficient * ourIBPAxisPlanePairOrbitMultiplicity target := by
  simp [ourIBPAxisPlanePairCoordinate]

/- The following three finite sums are the bounded certificate for the
second coordinate.  They are replayed by the Lean kernel rather than by an
external numerical oracle. -/
set_option maxRecDepth 100000 in
theorem source_ourIBPAxisPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      sourceLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (sourceLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem swapped_ourIBPAxisPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      swappedLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (swappedLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourIBPAxisPlanePairSignedWeight :
    (∑ field : Fin 7, ∑ h : Hypercubic4,
      (ourIBPLabeledTerm field).tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          ((ourIBPLabeledTerm field).hypercubicAct h) : ℚ)) = 16 := by
  decide +kernel

/-- The split-derivative orbit coordinate follows the commutator source
under the signed hypercubic action. -/
theorem ourIBPAxisPlanePairOrbitMultiplicity_source_action
    (h : Hypercubic4) :
    ourIBPAxisPlanePairOrbitMultiplicity
      (sourceSevenOrbit.hypercubicAct h) =
      (ourIBPAxisPlanePairMultiplicity
        (sourceLabeled.hypercubicAct h) : ℚ) := by
  simp [ourIBPAxisPlanePairOrbitMultiplicity, sourceSevenOrbit]

/-- The split-derivative orbit coordinate follows the swapped commutator
source under the signed hypercubic action. -/
theorem ourIBPAxisPlanePairOrbitMultiplicity_swapped_action
    (h : Hypercubic4) :
    ourIBPAxisPlanePairOrbitMultiplicity
      (swappedSevenOrbit.hypercubicAct h) =
      (ourIBPAxisPlanePairMultiplicity
        (swappedLabeled.hypercubicAct h) : ℚ) := by
  simp [ourIBPAxisPlanePairOrbitMultiplicity, swappedSevenOrbit]

/-- The split-derivative orbit coordinate follows one explicit IBP summand
under the signed hypercubic action. -/
theorem ourIBPAxisPlanePairOrbitMultiplicity_ourIBP_action
    (field : Fin 7) (h : Hypercubic4) :
    ourIBPAxisPlanePairOrbitMultiplicity
      ((ourIBPOrbit field).hypercubicAct h) =
      (ourIBPAxisPlanePairMultiplicity
        ((ourIBPLabeledTerm field).hypercubicAct h) : ℚ) := by
  simp [ourIBPAxisPlanePairOrbitMultiplicity, ourIBPOrbit]

/-- The selected split-derivative coordinate vanishes on the Reynolds
average of the commutator source. -/
theorem ourIBPAxisPlanePairCoordinate_reynolds_source :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single sourceSevenOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single sourceSevenOrbit (1 : ℚ))) =
        sourceLabeled.tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            (sourceLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single,
      ourIBPAxisPlanePairOrbitMultiplicity_source_action]
    simp [sourceSevenOrbit]
  simp_rw [hterm]
  rw [source_ourIBPAxisPlanePairSignedWeight]
  norm_num

/-- The selected split-derivative coordinate vanishes on the Reynolds
average of the swapped commutator source. -/
theorem ourIBPAxisPlanePairCoordinate_reynolds_swapped :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single swappedSevenOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single swappedSevenOrbit (1 : ℚ))) =
        swappedLabeled.tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            (swappedLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single,
      ourIBPAxisPlanePairOrbitMultiplicity_swapped_action]
    simp [swappedSevenOrbit]
  simp_rw [hterm]
  rw [swapped_ourIBPAxisPlanePairSignedWeight]
  norm_num

/-- The selected split-derivative coordinate vanishes on the Reynolds
average of the complete seven-field commutator component. -/
theorem ourIBPAxisPlanePairCoordinate_reynolds_coupledIncoming_fst :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2 coupledIncomingCommutatorVector.1) = 0 := by
  rw [coupledIncomingCommutatorVector_fst, LinearMap.map_sub,
    LinearMap.map_sub,
    ourIBPAxisPlanePairCoordinate_reynolds_source,
    ourIBPAxisPlanePairCoordinate_reynolds_swapped]
  norm_num

/-- The selected split-derivative coordinate takes the Reynolds average of
OUR complete explicit IBP row to the exact scalar `1 / 24`. -/
theorem ourIBPAxisPlanePairCoordinate_reynolds_ourIBP :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (∑ field : Fin 7, Finsupp.single (ourIBPOrbit field) (1 : ℚ))) =
      1 / 24 := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (field : Fin 7) (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (ourIBPOrbit field) (1 : ℚ))) =
        (ourIBPLabeledTerm field).tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            ((ourIBPLabeledTerm field).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single,
      ourIBPAxisPlanePairOrbitMultiplicity_ourIBP_action]
    simp [ourIBPOrbit]
  simp_rw [hterm]
  rw [← Finset.smul_sum, ourIBPAxisPlanePairSignedWeight]
  norm_num

/-- The exact seven-field projection of OUR explicit IBP row is precisely
the sum of its seven ordinary seven-field orbit targets. -/
theorem exactFieldSevenProjection_ourIBP :
    exactFieldSevenProjection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) =
      ∑ field : Fin 7, Finsupp.single (ourIBPOrbit field) 1 := by
  rw [orbitPhysicalRelationOperator_ourIBP, map_sum]
  apply Finset.sum_congr rfl
  intro field _
  exact exactFieldSevenProjection_ourIBPExactTarget_single field 1

/-- OUR signed-hypercubic invariant coordinate for the split-derivative IBP
pattern.  Its scale `24` is fixed by the kernel-reduced finite calculation. -/
def ourInvariantIBPAxisCoordinate : ExactFieldRelabelOrbitSpace →ₗ[ℚ] ℚ :=
  (24 : ℚ) •
    ((ourIBPAxisPlanePairCoordinate.comp
      (exactFieldSevenProjection.comp exactFieldOrbitReynolds)))

/-- OUR split-derivative invariant coordinate is unchanged by every signed
hypercubic action. -/
theorem ourInvariantIBPAxisCoordinate_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourInvariantIBPAxisCoordinate
      (signedExactFieldRelabelOrbitAction h value) =
      ourInvariantIBPAxisCoordinate value := by
  unfold ourInvariantIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldOrbitReynolds_action]

/-- The split-derivative invariant coordinate vanishes on the full concrete
covariant-commutator column for either relation policy. -/
theorem ourInvariantIBPAxisCoordinate_ourCommutator
    (policy : PhysicalRelationPolicy) :
    ourInvariantIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  unfold ourInvariantIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourCommutator_full,
    ourIBPAxisPlanePairCoordinate_reynolds_coupledIncoming_fst]
  norm_num

/-- The split-derivative invariant coordinate evaluates OUR explicit IBP
row to one. -/
theorem ourInvariantIBPAxisCoordinate_ourIBP :
    ourInvariantIBPAxisCoordinate
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 1 := by
  unfold ourInvariantIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourIBP,
    ourIBPAxisPlanePairCoordinate_reynolds_ourIBP]
  norm_num

/-- OUR two-coordinate invariant seven-field functional: the original
commutator compensator corrected by the independently normalized IBP
coordinate. -/
def ourTwoCoordinateInvariantSevenAxisCoordinate :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] ℚ :=
  ourInvariantSevenAxisCoordinate -
    (1 / 2 : ℚ) • ourInvariantIBPAxisCoordinate

/-- OUR two-coordinate functional remains signed-hypercubic invariant. -/
theorem ourTwoCoordinateInvariantSevenAxisCoordinate_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourTwoCoordinateInvariantSevenAxisCoordinate
      (signedExactFieldRelabelOrbitAction h value) =
      ourTwoCoordinateInvariantSevenAxisCoordinate value := by
  unfold ourTwoCoordinateInvariantSevenAxisCoordinate
  change ourInvariantSevenAxisCoordinate
      (signedExactFieldRelabelOrbitAction h value) -
      (1 / 2 : ℚ) * ourInvariantIBPAxisCoordinate
        (signedExactFieldRelabelOrbitAction h value) =
      ourInvariantSevenAxisCoordinate value -
        (1 / 2 : ℚ) * ourInvariantIBPAxisCoordinate value
  rw [ourInvariantSevenAxisCoordinate_signed_action,
    ourInvariantIBPAxisCoordinate_signed_action]

/-- The two-coordinate functional retains the forced value one on the full
concrete commutator. -/
theorem ourTwoCoordinateInvariantSevenAxisCoordinate_ourCommutator
    (policy : PhysicalRelationPolicy) :
    ourTwoCoordinateInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 1 := by
  unfold ourTwoCoordinateInvariantSevenAxisCoordinate
  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  rw [ourInvariantSevenAxisCoordinate_ourCommutator,
    ourInvariantIBPAxisCoordinate_ourCommutator]
  norm_num

/-- The two-coordinate functional cancels the explicit IBP obstruction
exactly. -/
theorem ourTwoCoordinateInvariantSevenAxisCoordinate_ourIBP :
    ourTwoCoordinateInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 := by
  unfold ourTwoCoordinateInvariantSevenAxisCoordinate
  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  rw [ourInvariantSevenAxisCoordinate_ourIBP,
    ourInvariantIBPAxisCoordinate_ourIBP]
  norm_num

/-- The split-derivative invariant coordinate vanishes on every typed
derivative-free eight-field inclusion. -/
theorem ourInvariantIBPAxisCoordinate_fieldEightExactEmbed_zero
    (value : FieldEightOrbitSpace) :
    ourInvariantIBPAxisCoordinate (fieldEightExactEmbed value) = 0 := by
  unfold ourInvariantIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_fieldEightExactEmbed]
  simp

/-- Both invariant seven-field coordinates vanish on typed derivative-free
eight-field inclusions. -/
theorem ourTwoCoordinateInvariantSevenAxisCoordinate_fieldEightExactEmbed_zero
    (value : FieldEightOrbitSpace) :
    ourTwoCoordinateInvariantSevenAxisCoordinate (fieldEightExactEmbed value) =
      0 := by
  unfold ourTwoCoordinateInvariantSevenAxisCoordinate
  simp only [LinearMap.sub_apply, LinearMap.smul_apply,
    ourInvariantSevenAxisCoordinate_fieldEightExactEmbed_zero,
    ourInvariantIBPAxisCoordinate_fieldEightExactEmbed_zero]
  norm_num

/-- OUR two-coordinate seven-field compensator, valued in the certified
eight-field trace quotient. -/
def ourTwoCoordinateInvariantSevenTraceCompensator :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ourTwoCoordinateInvariantSevenAxisCoordinate.smulRight
    literalIncomingCommutatorClass

/-- OUR two-coordinate compensator is signed-hypercubic invariant. -/
theorem ourTwoCoordinateInvariantSevenTraceCompensator_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourTwoCoordinateInvariantSevenTraceCompensator
      (signedExactFieldRelabelOrbitAction h value) =
      ourTwoCoordinateInvariantSevenTraceCompensator value := by
  simp only [ourTwoCoordinateInvariantSevenTraceCompensator,
    LinearMap.smulRight_apply,
    ourTwoCoordinateInvariantSevenAxisCoordinate_signed_action]

/-- OUR two-coordinate compensator retains the forced literal trace class on
the full concrete covariant commutator. -/
theorem ourTwoCoordinateInvariantSevenTraceCompensator_ourCommutator
    (policy : PhysicalRelationPolicy) :
    ourTwoCoordinateInvariantSevenTraceCompensator
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) =
      literalIncomingCommutatorClass := by
  simp only [ourTwoCoordinateInvariantSevenTraceCompensator,
    LinearMap.smulRight_apply,
    ourTwoCoordinateInvariantSevenAxisCoordinate_ourCommutator]
  simp

/-- OUR two-coordinate compensator vanishes on the explicit IBP row. -/
theorem ourTwoCoordinateInvariantSevenTraceCompensator_ourIBP_zero :
    ourTwoCoordinateInvariantSevenTraceCompensator
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 := by
  simp only [ourTwoCoordinateInvariantSevenTraceCompensator,
    LinearMap.smulRight_apply,
    ourTwoCoordinateInvariantSevenAxisCoordinate_ourIBP, zero_smul]

/-- OUR revised trace-order correction: the two-coordinate invariant
seven-field compensator minus the canonical eight-field trace coordinate. -/
def ourTwoCoordinateInvariantTraceOrderCorrection :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ourTwoCoordinateInvariantSevenTraceCompensator - exactFieldEightTraceProjection

/-- OUR revised correction is unchanged by every signed hypercubic action. -/
theorem ourTwoCoordinateInvariantTraceOrderCorrection_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (signedExactFieldRelabelOrbitAction h value) =
      ourTwoCoordinateInvariantTraceOrderCorrection value := by
  unfold ourTwoCoordinateInvariantTraceOrderCorrection
  change ourTwoCoordinateInvariantSevenTraceCompensator
      (signedExactFieldRelabelOrbitAction h value) -
      exactFieldEightTraceProjection
        (signedExactFieldRelabelOrbitAction h value) =
      ourTwoCoordinateInvariantSevenTraceCompensator value -
        exactFieldEightTraceProjection value
  rw [ourTwoCoordinateInvariantSevenTraceCompensator_signed_action,
    exactFieldEightTraceProjection_signed_action]

/-- OUR revised correction annihilates the full concrete covariant
commutator column for either relation policy. -/
theorem ourTwoCoordinateInvariantTraceOrderCorrection_ourCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  change ourTwoCoordinateInvariantSevenTraceCompensator
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) -
      exactFieldEightTraceProjection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0
  rw [ourTwoCoordinateInvariantSevenTraceCompensator_ourCommutator,
    exactFieldEightTraceProjection_ourCommutator]
  abel

/-- OUR revised correction annihilates the explicit full physical IBP row;
this is the precise repair of the one-coordinate obstruction. -/
theorem ourTwoCoordinateInvariantTraceOrderCorrection_ourIBP_zero :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 := by
  change ourTwoCoordinateInvariantSevenTraceCompensator
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) -
      exactFieldEightTraceProjection
        (orbitPhysicalRelationOperator .offShell
          (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0
  rw [ourTwoCoordinateInvariantSevenTraceCompensator_ourIBP_zero,
    exactFieldEightTraceProjection_ourIBP_zero]
  simp

/-- OUR revised compensator vanishes on any typed derivative-free eight-field
inclusion. -/
theorem ourTwoCoordinateInvariantSevenTraceCompensator_fieldEightExactEmbed_zero
    (value : FieldEightOrbitSpace) :
    ourTwoCoordinateInvariantSevenTraceCompensator (fieldEightExactEmbed value) =
      0 := by
  simp only [ourTwoCoordinateInvariantSevenTraceCompensator,
    LinearMap.smulRight_apply,
    ourTwoCoordinateInvariantSevenAxisCoordinate_fieldEightExactEmbed_zero,
    zero_smul]

/-- OUR revised correction annihilates every typed derivative-free
eight-field trace row. -/
theorem ourTwoCoordinateInvariantTraceOrderCorrection_fieldEightTraceRow_zero
    (generator : FieldEightTraceGenerator) :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (fieldEightExactEmbed (fieldEightPhysicalTraceRow generator)) = 0 := by
  change ourTwoCoordinateInvariantSevenTraceCompensator
      (fieldEightExactEmbed (fieldEightPhysicalTraceRow generator)) -
      exactFieldEightTraceProjection
        (fieldEightExactEmbed (fieldEightPhysicalTraceRow generator)) = 0
  rw [ourTwoCoordinateInvariantSevenTraceCompensator_fieldEightExactEmbed_zero]
  change 0 - exactFieldEightTraceClassMap
      (exactFieldEightProjection
        (fieldEightExactEmbed (fieldEightPhysicalTraceRow generator))) = 0
  rw [exactFieldEightProjection_fieldEightExactEmbed,
    ourExactFieldEightTraceClassMap_fieldEightPhysicalTraceRow_zero]
  simp

/-- OUR revised correction annihilates the actual full-carrier lift of every
derivative-free eight-field trace generator, for both physical policies. -/
theorem ourTwoCoordinateInvariantTraceOrderCorrection_liftedTraceGenerator_zero
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)) =
      0 := by
  rw [ourOrbitPhysicalRelationOperator_lift]
  exact ourTwoCoordinateInvariantTraceOrderCorrection_fieldEightTraceRow_zero
    generator

/-- OUR revised correction is unchanged by full exact-carrier Reynolds
averaging. -/
theorem ourTwoCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds
    (value : ExactFieldRelabelOrbitSpace) :
    ourTwoCoordinateInvariantTraceOrderCorrection (exactFieldOrbitReynolds value) =
      ourTwoCoordinateInvariantTraceOrderCorrection value := by
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  simp_rw [ourTwoCoordinateInvariantTraceOrderCorrection_signed_action]
  rw [Finset.sum_const, Finset.card_univ, Hypercubic4.card_hypercubic4]
  module

/-- OUR Reynolds-averaged explicit IBP row in the exact invariant carrier. -/
def ourInvariantIBPRow : exactFieldOrbitInvariantSubmodule :=
  ⟨exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)),
    exactFieldOrbitReynolds_invariant _⟩

/-- OUR averaged explicit IBP row belongs to the honest coordinate-free
off-shell joint invariant relation submodule. -/
theorem ourInvariantIBPRow_mem :
    ourInvariantIBPRow ∈ jointInvariantRelationSubmodule .offShell := by
  rw [mem_jointInvariantRelationSubmodule_iff]
  change exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) ∈
      orbitPhysicalRelationSubmodule .offShell
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  apply (orbitPhysicalRelationSubmodule .offShell).smul_mem
  apply Submodule.sum_mem
  intro h _
  apply orbitPhysicalRelationSubmodule_signed_invariant .offShell h
  exact ⟨Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1, rfl⟩

/-- The revised correction annihilates the actual invariant IBP member of
the coordinate-free off-shell joint relation space. -/
theorem ourTwoCoordinateInvariantTraceOrderCorrection_invariantIBP_zero :
    ourTwoCoordinateInvariantTraceOrderCorrection ourInvariantIBPRow.1 = 0 := by
  rw [show ourInvariantIBPRow.1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator .offShell
          (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) by rfl,
    ourTwoCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourTwoCoordinateInvariantTraceOrderCorrection_ourIBP_zero]

#print axioms derivativeAxisOrbitMultiplicity_source
#print axioms source_signedAxisWeight
#print axioms exactFieldSevenProjection_signed_action
#print axioms ourInvariantTraceOrderCorrection_ourCommutator_zero
#print axioms ourInvariantTraceOrderCorrection_liftedTraceGenerator_zero
#print axioms ourInvariantTraceOrderCorrection_ourIBP_ne_zero
#print axioms ourInvariantTraceOrderCorrection_reynolds_ourIBP_ne_zero
#print axioms derivativeAxisPlanePairMultiplicity_relabel
#print axioms ourIBPAxisPlanePairSignedWeight
#print axioms ourTwoCoordinateInvariantTraceOrderCorrection_ourCommutator_zero
#print axioms ourTwoCoordinateInvariantTraceOrderCorrection_ourIBP_zero
#print axioms ourTwoCoordinateInvariantTraceOrderCorrection_liftedTraceGenerator_zero
#print axioms ourInvariantIBPRow_mem
#print axioms ourTwoCoordinateInvariantTraceOrderCorrection_invariantIBP_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantRepair
