import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoupledQuotient

/-!
# OUR compensated trace dual on the local coupled commutator quotient

The concrete covariant-commutator column has a derivative part in the
seven-field sector and a curvature part in the eight-field sector.  This
module constructs an explicit coordinate on the derivative part and uses it
to compensate the canonical eight-field trace map.  The resulting linear map
annihilates the full coupled commutator row and descends through the local
coupled quotient.

This is a local cross-sector certificate.  It neither identifies the local
quotient with the full invariant relation quotient `J_p`, nor computes a
joint dimension, conditioning bound, or complete field/derivative census.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoupledDual

open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16ShuffleQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledColumn
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16SignedOrbitCoinvariants

/-- OUR labeled seven-field source sector. -/
abbrev sourceLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData ourFieldSevenCommutatorCarrier.2)

/-- OUR labeled seven-field sector with its two exact derivative positions
exchanged. -/
abbrev swappedLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData
      (swapExactDerivativePositions ourFieldSevenCommutatorCarrier
        ourFieldSevenCommutatorSite.outer ourFieldSevenCommutatorSite.inner).2)

/-- The multiplicity of a derivative-axis word in one labeled seven-field
sector. -/
def derivativeAxisWordMultiplicity (word : List (Fin 4))
    (sector : LabeledLocalWordSector 7 2) : ℕ :=
  ∑ field : Fin 7,
    if List.ofFn (sector.decoration.1 field).derivativeAxis = word then 1 else 0

/-- This multiplicity is invariant under field relabeling. -/
theorem derivativeAxisWordMultiplicity_relabel
    (word : List (Fin 4)) (rename : Equiv.Perm (Fin 7))
    (sector : LabeledLocalWordSector 7 2) :
    derivativeAxisWordMultiplicity word
        (LabeledLocalWordSector.relabel rename sector) =
      derivativeAxisWordMultiplicity word sector := by
  unfold derivativeAxisWordMultiplicity
  exact Equiv.sum_comp rename.symm
    (fun field =>
      if List.ofFn (sector.decoration.1 field).derivativeAxis = word then 1 else 0)

/-- OUR source has one derivative-axis word `[0, 2]`. -/
theorem sourceAxisMultiplicity :
    derivativeAxisWordMultiplicity [0, 2] sourceLabeled = 1 := by
  decide +kernel

/-- OUR swapped source has no derivative-axis word `[0, 2]`. -/
theorem swappedAxisMultiplicity :
    derivativeAxisWordMultiplicity [0, 2] swappedLabeled = 0 := by
  decide +kernel

/-- OUR source and swapped source are not related by field relabeling. -/
theorem sourceSwapped_not_relabel : ¬ ∃ rename : Equiv.Perm (Fin 7),
    LabeledLocalWordSector.relabel rename swappedLabeled = sourceLabeled := by
  rintro ⟨rename, hrename⟩
  have hcount := congrArg (derivativeAxisWordMultiplicity [0, 2]) hrename
  rw [derivativeAxisWordMultiplicity_relabel,
    swappedAxisMultiplicity, sourceAxisMultiplicity] at hcount
  norm_num at hcount

/-- OUR source and swapped source determine distinct seven-field relabel
orbits. -/
theorem sourceSwapped_not_orbit : ¬ MulAction.orbitRel (Equiv.Perm (Fin 7))
    (LabeledLocalWordSector 7 2) sourceLabeled swappedLabeled := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  intro horbit
  rcases horbit with ⟨rename, hrename⟩
  change LabeledLocalWordSector.relabel rename swappedLabeled = sourceLabeled at hrename
  exact sourceSwapped_not_relabel ⟨rename, hrename⟩

/-- OUR source seven-field relabel orbit. -/
abbrev sourceSevenOrbit : FieldSevenOrbitCarrier := Quotient.mk _ sourceLabeled

/-- OUR swapped seven-field relabel orbit. -/
abbrev swappedSevenOrbit : FieldSevenOrbitCarrier := Quotient.mk _ swappedLabeled

/-- The exact two-band projection of a seven-field orbit is supported in
the first component. -/
theorem exactFieldSevenEightProjectionBasis_of_seven
    (orbit : FieldSevenOrbitCarrier) :
    exactFieldSevenEightProjectionBasis
        (⟨ourSevenFieldCount, orbit⟩ : ExactFieldRelabelOrbitCarrier) =
      (Finsupp.single orbit (1 : ℚ), 0) := by
  simp [exactFieldSevenEightProjectionBasis, exactFieldSevenOrbitCast_self]

/-- The first component of the exact two-band projection vanishes on either
curvature insertion. -/
theorem exactFieldSevenEightProjectionBasis_fst_of_insertion
    (side : CurvatureInsertionSide) :
    (exactFieldSevenEightProjectionBasis
      (ourCommutatorInsertionExactTarget side)).1 = 0 := by
  simp [exactFieldSevenEightProjectionBasis, ourSevenFieldCount,
    ourEightFieldCount]

/-- OUR source exact target is its corresponding seven-field orbit. -/
theorem sourceExactTarget_eq_seven :
    ourCommutatorSourceExactTarget =
      (⟨ourSevenFieldCount, sourceSevenOrbit⟩ : ExactFieldRelabelOrbitCarrier) := rfl

/-- OUR swapped exact target is its corresponding seven-field orbit. -/
theorem swappedExactTarget_eq_seven :
    ourCommutatorSwappedExactTarget =
      (⟨ourSevenFieldCount, swappedSevenOrbit⟩ : ExactFieldRelabelOrbitCarrier) := rfl

/-- OUR source and swapped seven-field orbit representatives are distinct. -/
theorem sourceSevenOrbit_ne_swappedSevenOrbit :
    sourceSevenOrbit ≠ swappedSevenOrbit := by
  intro horbit
  exact sourceSwapped_not_orbit (Quotient.exact horbit)

/-- The source-minus-swapped seven-field vector is nonzero. -/
theorem sourceSevenOrbit_difference_ne_zero :
    Finsupp.single sourceSevenOrbit (1 : ℚ) -
      Finsupp.single swappedSevenOrbit (1 : ℚ) ≠ 0 := by
  intro hzero
  have hcoefficient := congrArg
    (fun value : FieldSevenOrbitSpace => value sourceSevenOrbit) hzero
  simp [sourceSevenOrbit_ne_swappedSevenOrbit] at hcoefficient

/-- The first component of OUR full coupled row is exactly the nonzero
source-minus-swapped seven-field vector. -/
theorem coupledIncomingCommutatorVector_fst : coupledIncomingCommutatorVector.1 =
    Finsupp.single sourceSevenOrbit (1 : ℚ) -
      Finsupp.single swappedSevenOrbit (1 : ℚ) := by
  rw [coupledIncomingCommutatorVector, sourceExactTarget_eq_seven,
    swappedExactTarget_eq_seven]
  rw [exactFieldSevenEightProjectionBasis_of_seven,
    exactFieldSevenEightProjectionBasis_of_seven]
  change Finsupp.single sourceSevenOrbit (1 : ℚ) -
      Finsupp.single swappedSevenOrbit (1 : ℚ) -
      (exactFieldSevenEightProjectionBasis
        (ourCommutatorInsertionExactTarget CurvatureInsertionSide.before)).1 +
      (exactFieldSevenEightProjectionBasis
        (ourCommutatorInsertionExactTarget CurvatureInsertionSide.after)).1 = _
  rw [show (exactFieldSevenEightProjectionBasis
      (ourCommutatorInsertionExactTarget CurvatureInsertionSide.before)).1 = 0 by
        exact exactFieldSevenEightProjectionBasis_fst_of_insertion _,
    show (exactFieldSevenEightProjectionBasis
      (ourCommutatorInsertionExactTarget CurvatureInsertionSide.after)).1 = 0 by
        exact exactFieldSevenEightProjectionBasis_fst_of_insertion _]
  abel

/-- The first component of OUR full coupled row is nonzero. -/
theorem coupledIncomingCommutatorVector_fst_ne_zero :
    coupledIncomingCommutatorVector.1 ≠ 0 := by
  rw [coupledIncomingCommutatorVector_fst]
  exact sourceSevenOrbit_difference_ne_zero

/-- OUR coordinate functional at the source seven-field orbit. -/
def sourceSevenCoordinate : FieldSevenOrbitSpace →ₗ[ℚ] ℚ :=
  Finsupp.lapply sourceSevenOrbit

/-- OUR source coordinate evaluates the first coupled-row component to one. -/
theorem sourceSevenCoordinate_coupledIncomingCommutatorVector_fst :
    sourceSevenCoordinate coupledIncomingCommutatorVector.1 = 1 := by
  have hreverse : swappedSevenOrbit ≠ sourceSevenOrbit :=
    sourceSevenOrbit_ne_swappedSevenOrbit.symm
  rw [coupledIncomingCommutatorVector_fst]
  simp [sourceSevenCoordinate, hreverse]

/-- OUR seven-field compensation into the certified eight-field trace
quotient. -/
def coupledSevenTraceCompensator :
    FieldSevenOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  sourceSevenCoordinate.smulRight literalIncomingCommutatorClass

/-- OUR seven-field compensator sends the first coupled-row component to the
literal incoming trace class. -/
theorem coupledSevenTraceCompensator_coupledIncomingCommutatorVector_fst :
    coupledSevenTraceCompensator coupledIncomingCommutatorVector.1 =
      literalIncomingCommutatorClass := by
  simp only [coupledSevenTraceCompensator, LinearMap.smulRight_apply]
  rw [sourceSevenCoordinate_coupledIncomingCommutatorVector_fst]
  simp

/-- OUR compensated trace dual: the seven-field coordinate compensation
minus the canonical eight-field trace class map. -/
def coupledIncomingTraceDual :
    (FieldSevenOrbitSpace × FieldEightOrbitSpace) →ₗ[ℚ]
      FieldEightPhysicalTraceQuotient :=
  (coupledSevenTraceCompensator.comp
    (LinearMap.fst ℚ FieldSevenOrbitSpace FieldEightOrbitSpace)) -
  (exactFieldEightTraceClassMap.comp
    (LinearMap.snd ℚ FieldSevenOrbitSpace FieldEightOrbitSpace))

/-- OUR compensated trace dual annihilates the complete local coupled
commutator row. -/
theorem coupledIncomingTraceDual_coupledIncomingCommutatorVector :
    coupledIncomingTraceDual coupledIncomingCommutatorVector = 0 := by
  change coupledSevenTraceCompensator coupledIncomingCommutatorVector.1 -
      exactFieldEightTraceClassMap coupledIncomingCommutatorVector.2 = 0
  rw [coupledSevenTraceCompensator_coupledIncomingCommutatorVector_fst,
    coupledIncomingCommutatorVector_traceClass]
  abel

/-- OUR compensated trace dual descended through the local coupled
commutator quotient. -/
def coupledIncomingQuotientTraceDual :
    CoupledIncomingQuotient →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  coupledIncomingRelationSubmodule.liftQ coupledIncomingTraceDual (by
    rw [coupledIncomingRelationSubmodule_eq_span]
    rw [Submodule.span_le]
    intro vector hvector
    rw [Set.mem_singleton_iff] at hvector
    subst vector
    exact coupledIncomingTraceDual_coupledIncomingCommutatorVector)

/-- Composing OUR descended dual with the local quotient map recovers the
explicit compensated trace dual. -/
theorem coupledIncomingQuotientTraceDual_comp_quotientMap :
    coupledIncomingQuotientTraceDual.comp coupledIncomingQuotientMap =
      coupledIncomingTraceDual := by
  exact coupledIncomingRelationSubmodule.liftQ_mkQ
    coupledIncomingTraceDual _

#print axioms sourceSwapped_not_orbit
#print axioms coupledIncomingCommutatorVector_fst
#print axioms coupledIncomingCommutatorVector_fst_ne_zero
#print axioms coupledIncomingTraceDual_coupledIncomingCommutatorVector
#print axioms coupledIncomingQuotientTraceDual_comp_quotientMap

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoupledDual
