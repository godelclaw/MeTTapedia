import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction

/-!
# OUR trace-topology fourth-coordinate repair

The preceding local obstruction is not repaired by a bare trace-cycle count:
the signed hypercubic average of such a scalar vanishes.  This module instead
gates the existing derivative-axis character by the relabel-invariant presence
of a two-cycle in the trace permutation.  On the canonical polarized
`SU(2)` trace-anticommutator row, the source and adjacent-swap terms have
cycle type `{7}`, whereas the split term has type `{2,5}`.  The gated
character therefore has the exact signed weights `0`, `0`, and `32`.

This is an OUR finite repair of that one canonical trace-topology obstruction.
It does not assert descent through the complete physical relation submodule,
complete joint rank, or Wilson-functional analytic coordinates.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderTraceTopologyRepair

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
open HypercubicDimension16SU2TraceRelations
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
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction

/-- OUR trace-topology-sensitive axis multiplicity.  It retains the selected
derivative-axis character only when the trace permutation has one two-cycle.
The cycle count is invariant under uniform field relabeling. -/
def ourTwoCycleTraceAxisMultiplicity
    (sector : LabeledLocalWordSector 7 2) : ℕ :=
  if sector.trace.cycleType.count 2 = 1 then
    derivativeAxisWordMultiplicity [0, 2] sector
  else 0

/-- Uniform relabeling conjugates the trace permutation and hence preserves
its cycle type. -/
theorem ourTraceCycleType_relabel
    (rename : Equiv.Perm (Fin 7))
    (sector : LabeledLocalWordSector 7 2) :
    (sector.relabel rename).trace.cycleType = sector.trace.cycleType := by
  change (show Equiv.Perm (Fin 7) from
    rename.symm.trans (sector.trace.trans rename)).cycleType = _
  convert Equiv.Perm.cycleType_conj (σ := sector.trace) (τ := rename) using 1
  ext field
  rfl

/-- OUR gated multiplicity descends through ordinary field relabeling. -/
theorem ourTwoCycleTraceAxisMultiplicity_relabel
    (rename : Equiv.Perm (Fin 7))
    (sector : LabeledLocalWordSector 7 2) :
    ourTwoCycleTraceAxisMultiplicity (sector.relabel rename) =
      ourTwoCycleTraceAxisMultiplicity sector := by
  unfold ourTwoCycleTraceAxisMultiplicity
  rw [ourTraceCycleType_relabel]
  simp [derivativeAxisWordMultiplicity_relabel]

/-- OUR ordinary seven-field orbit scalar induced by the gated character. -/
def ourTwoCycleTraceAxisOrbitMultiplicity : FieldSevenOrbitCarrier → ℚ :=
  Quotient.lift (fun sector =>
    (ourTwoCycleTraceAxisMultiplicity sector : ℚ)) (by
      intro left right horbit
      change MulAction.orbitRel (Equiv.Perm (Fin 7))
        (LabeledLocalWordSector 7 2) left right at horbit
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at horbit
      rcases horbit with ⟨rename, hrename⟩
      change LabeledLocalWordSector.relabel rename right = left at hrename
      rw [← hrename]
      exact_mod_cast ourTwoCycleTraceAxisMultiplicity_relabel rename right)

/-- OUR linear coordinate on the seven-field ordinary-orbit space. -/
def ourTwoCycleTraceAxisCoordinate : FieldSevenOrbitSpace →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ ourTwoCycleTraceAxisOrbitMultiplicity

@[simp] theorem ourTwoCycleTraceAxisCoordinate_single
    (target : FieldSevenOrbitCarrier) (coefficient : ℚ) :
    ourTwoCycleTraceAxisCoordinate (Finsupp.single target coefficient) =
      coefficient * ourTwoCycleTraceAxisOrbitMultiplicity target := by
  simp [ourTwoCycleTraceAxisCoordinate]

/-- OUR coordinate follows a labeled sector through the signed hypercubic
action. -/
theorem ourTwoCycleTraceAxisOrbitMultiplicity_action
    (sector : LabeledLocalWordSector 7 2) (h : Hypercubic4) :
    ourTwoCycleTraceAxisOrbitMultiplicity
      (FieldRelabelOrbitCarrier.hypercubicAct h (Quotient.mk _ sector)) =
      (ourTwoCycleTraceAxisMultiplicity (sector.hypercubicAct h) : ℚ) := by
  simp [ourTwoCycleTraceAxisOrbitMultiplicity]

/-- A bounded signed-weight certificate gives the corresponding Reynolds
coordinate exactly. -/
theorem ourTwoCycleTraceAxisCoordinate_reynolds_single
    (sector : LabeledLocalWordSector 7 2) (weight : ℚ)
    (hweight :
      (∑ h : Hypercubic4,
        sector.tensorSign h *
          (ourTwoCycleTraceAxisMultiplicity (sector.hypercubicAct h) : ℚ)) =
        weight) :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (Quotient.mk _ sector : FieldSevenOrbitCarrier) (1 : ℚ))) =
      weight / 384 := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourTwoCycleTraceAxisCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (Quotient.mk _ sector : FieldSevenOrbitCarrier)
            (1 : ℚ))) =
        sector.tensorSign h *
          (ourTwoCycleTraceAxisMultiplicity (sector.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourTwoCycleTraceAxisCoordinate_single,
      ourTwoCycleTraceAxisOrbitMultiplicity_action]
    simp
  simp_rw [hterm]
  rw [hweight]
  ring

/- The following three bounded kernel computations isolate the repaired
trace-topology signal in the canonical `SU(2)` row. -/
set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorBase_twoCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorBaseLabeled.tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity
          (ourTraceAnticommutatorBaseLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorSwap_twoCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorSwapLabeled.tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity
          (ourTraceAnticommutatorSwapLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorSplit_twoCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorSplitLabeled.tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity
          (ourTraceAnticommutatorSplitLabeled.hypercubicAct h) : ℚ)) = 32 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The gated coordinate vanishes on the source trace wiring. -/
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourTraceAnticommutatorBase :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorBaseOrbit (1 : ℚ))) = 0 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourTraceAnticommutatorBaseLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTwoCycleTraceAxisCoordinate_reynolds_single
    ourTraceAnticommutatorBaseLabeled 0
    ourTraceAnticommutatorBase_twoCycleTraceAxisSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
/-- The gated coordinate vanishes on the adjacent-swap trace wiring. -/
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourTraceAnticommutatorSwap :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorSwapOrbit (1 : ℚ))) = 0 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourTraceAnticommutatorSwapLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTwoCycleTraceAxisCoordinate_reynolds_single
    ourTraceAnticommutatorSwapLabeled 0
    ourTraceAnticommutatorSwap_twoCycleTraceAxisSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
/-- The gated coordinate is `1 / 12` on the split trace wiring. -/
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourTraceAnticommutatorSplit :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorSplitOrbit (1 : ℚ))) = 1 / 12 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourTraceAnticommutatorSplitLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 1 / 12
  rw [ourTwoCycleTraceAxisCoordinate_reynolds_single
    ourTraceAnticommutatorSplitLabeled 32
    ourTraceAnticommutatorSplit_twoCycleTraceAxisSignedWeight]
  norm_num

/-- The canonical trace-anticommutator row has gated scalar `-1 / 12`. -/
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourTraceAnticommutator :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorBaseOrbit (1 : ℚ) +
          Finsupp.single ourTraceAnticommutatorSwapOrbit (1 : ℚ) -
            Finsupp.single ourTraceAnticommutatorSplitOrbit (1 : ℚ))) =
      -1 / 12 := by
  simp only [map_sub, map_add,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourTraceAnticommutatorBase,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourTraceAnticommutatorSwap,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourTraceAnticommutatorSplit]
  norm_num

/-- OUR scaled fourth invariant coordinate.  The scale `12` makes its value
on the complete canonical trace-anticommutator row equal to `-1`. -/
def ourInvariantTwoCycleTraceAxisCoordinate :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] ℚ :=
  (12 : ℚ) •
    (ourTwoCycleTraceAxisCoordinate.comp
      (exactFieldSevenProjection.comp exactFieldOrbitReynolds))

/-- OUR fourth scalar coordinate is signed-hypercubic invariant. -/
theorem ourInvariantTwoCycleTraceAxisCoordinate_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourInvariantTwoCycleTraceAxisCoordinate
      (signedExactFieldRelabelOrbitAction h value) =
      ourInvariantTwoCycleTraceAxisCoordinate value := by
  unfold ourInvariantTwoCycleTraceAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldOrbitReynolds_action]

/-- The fourth scalar coordinate detects the canonical trace-anticommutator
row with its normalized value `-1`. -/
theorem ourInvariantTwoCycleTraceAxisCoordinate_ourTraceAnticommutator
    (policy : PhysicalRelationPolicy) :
    ourInvariantTwoCycleTraceAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      -1 := by
  unfold ourInvariantTwoCycleTraceAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourTraceAnticommutator,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourTraceAnticommutator]
  norm_num

/-- OUR fourth trace-class contribution, valued in the certified incoming
trace class. -/
def ourTwoCycleTraceInvariantTraceContribution :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ((1 / 2 : ℚ) • ourInvariantTwoCycleTraceAxisCoordinate).smulRight
    literalIncomingCommutatorClass

/-- OUR four-coordinate finite correction. -/
def ourFourCoordinateInvariantTraceOrderCorrection :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ourThreeCoordinateInvariantTraceOrderCorrection +
    ourTwoCycleTraceInvariantTraceContribution

/-- The fourth contribution cancels the exact canonical trace-topology
obstruction. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 := by
  unfold ourFourCoordinateInvariantTraceOrderCorrection
    ourTwoCycleTraceInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator,
    ourInvariantTwoCycleTraceAxisCoordinate_ourTraceAnticommutator]
  module

/-- OUR fourth coordinate, like every signed-hypercubic invariant linear
functional, is unchanged by exact-field Reynolds averaging. -/
theorem ourInvariantTwoCycleTraceAxisCoordinate_exactFieldOrbitReynolds
    (value : ExactFieldRelabelOrbitSpace) :
    ourInvariantTwoCycleTraceAxisCoordinate (exactFieldOrbitReynolds value) =
      ourInvariantTwoCycleTraceAxisCoordinate value := by
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  simp_rw [ourInvariantTwoCycleTraceAxisCoordinate_signed_action]
  rw [Finset.sum_const, Finset.card_univ, Hypercubic4.card_hypercubic4]
  module

/-- OUR four-coordinate correction is unchanged by exact-field Reynolds
averaging. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds
    (value : ExactFieldRelabelOrbitSpace) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (exactFieldOrbitReynolds value) =
      ourFourCoordinateInvariantTraceOrderCorrection value := by
  unfold ourFourCoordinateInvariantTraceOrderCorrection
    ourTwoCycleTraceInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply]
  rw [ourThreeCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourInvariantTwoCycleTraceAxisCoordinate_exactFieldOrbitReynolds]

/-- The repaired correction annihilates the actual Reynolds-averaged
canonical trace-anticommutator member of the coordinate-free relation space. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (ourInvariantTraceAnticommutatorRow policy).1 = 0 := by
  rw [show (ourInvariantTraceAnticommutatorRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) by
        rfl,
    ourFourCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourFourCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator_zero]

/-- A zero signed weight gives a zero Reynolds scalar. -/
theorem ourTwoCycleTraceAxisCoordinate_reynolds_single_zero
    (sector : LabeledLocalWordSector 7 2)
    (hweight :
      (∑ h : Hypercubic4,
        sector.tensorSign h *
          (ourTwoCycleTraceAxisMultiplicity (sector.hypercubicAct h) : ℚ)) =
        0) :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (Quotient.mk _ sector : FieldSevenOrbitCarrier) (1 : ℚ))) =
      0 := by
  rw [ourTwoCycleTraceAxisCoordinate_reynolds_single sector 0 hweight]
  norm_num

/- The next certificates recheck the already-passed commutator and the two
explicit IBP rows against the trace-topology coordinate. -/
set_option maxRecDepth 100000 in
theorem source_twoCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      sourceLabeled.tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity (sourceLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem swapped_twoCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      swappedLabeled.tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity (swappedLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourIBP_twoCycleTraceAxisSignedWeight (field : Fin 7) :
    (∑ h : Hypercubic4,
      (ourIBPLabeledTerm field).tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity
          ((ourIBPLabeledTerm field).hypercubicAct h) : ℚ)) = 0 := by
  fin_cases field <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourSecondIBP_twoCycleTraceAxisSignedWeight (field : Fin 7) :
    (∑ h : Hypercubic4,
      (ourSecondIBPLabeledTerm field).tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity
          ((ourSecondIBPLabeledTerm field).hypercubicAct h) : ℚ)) = 0 := by
  fin_cases field <;> decide +kernel

set_option maxRecDepth 100000 in
theorem ourTwoCycleTraceAxisCoordinate_reynolds_source :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single sourceSevenOrbit (1 : ℚ))) = 0 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (Quotient.mk _ sourceLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  exact ourTwoCycleTraceAxisCoordinate_reynolds_single_zero sourceLabeled
    source_twoCycleTraceAxisSignedWeight

set_option maxRecDepth 100000 in
theorem ourTwoCycleTraceAxisCoordinate_reynolds_swapped :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single swappedSevenOrbit (1 : ℚ))) = 0 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (Quotient.mk _ swappedLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  exact ourTwoCycleTraceAxisCoordinate_reynolds_single_zero swappedLabeled
    swapped_twoCycleTraceAxisSignedWeight

theorem ourTwoCycleTraceAxisCoordinate_reynolds_coupledIncoming_fst :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2 coupledIncomingCommutatorVector.1) = 0 := by
  rw [coupledIncomingCommutatorVector_fst, LinearMap.map_sub,
    LinearMap.map_sub,
    ourTwoCycleTraceAxisCoordinate_reynolds_source,
    ourTwoCycleTraceAxisCoordinate_reynolds_swapped]
  norm_num

/-- The new trace-topology scalar vanishes on the complete commutator row. -/
theorem ourInvariantTwoCycleTraceAxisCoordinate_ourCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantTwoCycleTraceAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  unfold ourInvariantTwoCycleTraceAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourCommutator_full,
    ourTwoCycleTraceAxisCoordinate_reynolds_coupledIncoming_fst]
  norm_num

set_option maxRecDepth 100000 in
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourIBP
    (field : Fin 7) :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (ourIBPOrbit field) (1 : ℚ))) = 0 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ (ourIBPLabeledTerm field) : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  exact ourTwoCycleTraceAxisCoordinate_reynolds_single_zero
    (ourIBPLabeledTerm field) (ourIBP_twoCycleTraceAxisSignedWeight field)

theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourIBPRow :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (∑ field : Fin 7, Finsupp.single (ourIBPOrbit field) (1 : ℚ))) = 0 := by
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro field _
  exact ourTwoCycleTraceAxisCoordinate_reynolds_ourIBP field

/-- The new trace-topology scalar vanishes on the first explicit IBP row. -/
theorem ourInvariantTwoCycleTraceAxisCoordinate_ourIBP_zero :
    ourInvariantTwoCycleTraceAxisCoordinate
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 := by
  unfold ourInvariantTwoCycleTraceAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourIBP,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourIBPRow]
  norm_num

set_option maxRecDepth 100000 in
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourSecondIBP
    (field : Fin 7) :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (ourSecondIBPOrbit field) (1 : ℚ))) = 0 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ (ourSecondIBPLabeledTerm field) : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  exact ourTwoCycleTraceAxisCoordinate_reynolds_single_zero
    (ourSecondIBPLabeledTerm field)
    (ourSecondIBP_twoCycleTraceAxisSignedWeight field)

theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourSecondIBPRow :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (∑ field : Fin 7, Finsupp.single (ourSecondIBPOrbit field) (1 : ℚ))) =
      0 := by
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro field _
  exact ourTwoCycleTraceAxisCoordinate_reynolds_ourSecondIBP field

/-- The new trace-topology scalar vanishes on the second explicit IBP row. -/
theorem ourInvariantTwoCycleTraceAxisCoordinate_ourSecondIBP_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantTwoCycleTraceAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 := by
  unfold ourInvariantTwoCycleTraceAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSecondIBP,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourSecondIBPRow]
  norm_num

/-- The four-coordinate correction retains the existing commutator check. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_ourCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  unfold ourFourCoordinateInvariantTraceOrderCorrection
    ourTwoCycleTraceInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourCommutator_zero,
    ourInvariantTwoCycleTraceAxisCoordinate_ourCommutator_zero]
  simp

/-- The four-coordinate correction retains the first explicit IBP check. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_ourIBP_zero :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 := by
  unfold ourFourCoordinateInvariantTraceOrderCorrection
    ourTwoCycleTraceInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourIBP_zero,
    ourInvariantTwoCycleTraceAxisCoordinate_ourIBP_zero]
  simp

/-- The four-coordinate correction retains the second explicit IBP check. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_ourSecondIBP_zero
    (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 := by
  unfold ourFourCoordinateInvariantTraceOrderCorrection
    ourTwoCycleTraceInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourSecondIBP_zero,
    ourInvariantTwoCycleTraceAxisCoordinate_ourSecondIBP_zero]
  simp

/- The Bianchi and on-shell EOM rows retain a single trace cycle in every
nonzero normalized summand.  These bounded certificates recheck that fact at
the level of the actual signed trace-topology coordinate. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourBianchiBase_twoCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourBianchiBaseLabeled.tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity
          (ourBianchiBaseLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourBianchiRotateOne_twoCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourBianchiRotateOneLabeled.tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity
          (ourBianchiRotateOneLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourBianchiRotateTwo_twoCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourBianchiRotateTwoLabeled.tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity
          (ourBianchiRotateTwoLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourBianchiBase :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiBaseOrbit (1 : ℚ))) = 0 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourBianchiBaseLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  exact ourTwoCycleTraceAxisCoordinate_reynolds_single_zero
    ourBianchiBaseLabeled ourBianchiBase_twoCycleTraceAxisSignedWeight

set_option maxRecDepth 100000 in
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourBianchiRotateOne :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateOneOrbit (1 : ℚ))) = 0 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourBianchiRotateOneLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  exact ourTwoCycleTraceAxisCoordinate_reynolds_single_zero
    ourBianchiRotateOneLabeled
    ourBianchiRotateOne_twoCycleTraceAxisSignedWeight

set_option maxRecDepth 100000 in
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourBianchiRotateTwo :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateTwoOrbit (1 : ℚ))) = 0 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourBianchiRotateTwoLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  exact ourTwoCycleTraceAxisCoordinate_reynolds_single_zero
    ourBianchiRotateTwoLabeled
    ourBianchiRotateTwo_twoCycleTraceAxisSignedWeight

theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourBianchiRotateOne_neg :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateOneOrbit (-1 : ℚ))) = 0 := by
  rw [show Finsupp.single ourBianchiRotateOneOrbit (-1 : ℚ) =
      -Finsupp.single ourBianchiRotateOneOrbit (1 : ℚ) by simp,
    map_neg, map_neg,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourBianchiRotateOne]
  simp

/-- The trace-topology scalar vanishes on the complete Bianchi row. -/
theorem ourInvariantTwoCycleTraceAxisCoordinate_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantTwoCycleTraceAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  unfold ourInvariantTwoCycleTraceAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourBianchi]
  simp only [LinearMap.map_add,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourBianchiBase,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourBianchiRotateOne_neg,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourBianchiRotateTwo]
  norm_num

/-- The four-coordinate correction retains the explicit Bianchi check. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  unfold ourFourCoordinateInvariantTraceOrderCorrection
    ourTwoCycleTraceInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourBianchi_zero,
    ourInvariantTwoCycleTraceAxisCoordinate_ourBianchi_zero]
  simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourEOMZero_twoCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourEOMZeroLabeled.tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity
          (ourEOMZeroLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourEOMOne_twoCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourEOMOneLabeled.tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity
          (ourEOMOneLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourEOMThree_twoCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourEOMThreeLabeled.tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity
          (ourEOMThreeLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourEOMZero :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMZeroOrbit (1 : ℚ))) = 0 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourEOMZeroLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  exact ourTwoCycleTraceAxisCoordinate_reynolds_single_zero
    ourEOMZeroLabeled ourEOMZero_twoCycleTraceAxisSignedWeight

set_option maxRecDepth 100000 in
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourEOMOne :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMOneOrbit (1 : ℚ))) = 0 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourEOMOneLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  exact ourTwoCycleTraceAxisCoordinate_reynolds_single_zero
    ourEOMOneLabeled ourEOMOne_twoCycleTraceAxisSignedWeight

set_option maxRecDepth 100000 in
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourEOMThree :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMThreeOrbit (1 : ℚ))) = 0 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourEOMThreeLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  exact ourTwoCycleTraceAxisCoordinate_reynolds_single_zero
    ourEOMThreeLabeled ourEOMThree_twoCycleTraceAxisSignedWeight

theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourEOMThree_neg :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMThreeOrbit (-1 : ℚ))) = 0 := by
  rw [show Finsupp.single ourEOMThreeOrbit (-1 : ℚ) =
      -Finsupp.single ourEOMThreeOrbit (1 : ℚ) by simp,
    map_neg, map_neg,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourEOMThree]
  simp

/-- The trace-topology scalar vanishes on the complete on-shell EOM row. -/
theorem ourInvariantTwoCycleTraceAxisCoordinate_ourEOM_zero :
    ourInvariantTwoCycleTraceAxisCoordinate
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  unfold ourInvariantTwoCycleTraceAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourEOM]
  simp only [LinearMap.map_add,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourEOMZero,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourEOMOne,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourEOMThree_neg]
  norm_num

/-- The four-coordinate correction retains the explicit on-shell EOM check. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_ourEOM_zero :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  unfold ourFourCoordinateInvariantTraceOrderCorrection
    ourTwoCycleTraceInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourEOM_zero,
    ourInvariantTwoCycleTraceAxisCoordinate_ourEOM_zero]
  simp

/-- The trace-topology scalar vanishes on the typed derivative-free
eight-field inclusion before any trace relation is imposed. -/
theorem ourInvariantTwoCycleTraceAxisCoordinate_fieldEightExactEmbed_zero
    (value : FieldEightOrbitSpace) :
    ourInvariantTwoCycleTraceAxisCoordinate (fieldEightExactEmbed value) = 0 := by
  unfold ourInvariantTwoCycleTraceAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_fieldEightExactEmbed]
  simp

/-- The four-coordinate correction retains every derivative-free eight-field
trace relation in the explicit lifted family. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_liftedTraceGenerator_zero
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)) =
      0 := by
  unfold ourFourCoordinateInvariantTraceOrderCorrection
    ourTwoCycleTraceInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourThreeCoordinateInvariantTraceOrderCorrection_liftedTraceGenerator_zero]
  rw [show orbitPhysicalRelationOperator policy
      (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1) =
      fieldEightExactEmbed (fieldEightPhysicalTraceRow generator) by
        exact ourOrbitPhysicalRelationOperator_lift policy generator,
    ourInvariantTwoCycleTraceAxisCoordinate_fieldEightExactEmbed_zero]
  simp

/-- The four-coordinate correction retains the actual Reynolds-averaged
commutator member of the coordinate-free joint relation space. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_invariantCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (ourInvariantCommutatorRow policy).1 = 0 := by
  rw [show (ourInvariantCommutatorRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) by rfl,
    ourFourCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourFourCoordinateInvariantTraceOrderCorrection_ourCommutator_zero]

/-- The four-coordinate correction retains the actual Reynolds-averaged
first-IBP member. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_invariantIBP_zero :
    ourFourCoordinateInvariantTraceOrderCorrection ourInvariantIBPRow.1 = 0 := by
  rw [show ourInvariantIBPRow.1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator .offShell
          (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) by rfl,
    ourFourCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourFourCoordinateInvariantTraceOrderCorrection_ourIBP_zero]

/-- The four-coordinate correction retains the actual Reynolds-averaged
second-IBP member under either policy. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_invariantSecondIBP_zero
    (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (ourInvariantSecondIBPRow policy).1 = 0 := by
  rw [show (ourInvariantSecondIBPRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) by rfl,
    ourFourCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourFourCoordinateInvariantTraceOrderCorrection_ourSecondIBP_zero]

/-- The four-coordinate correction retains the actual Reynolds-averaged
Bianchi member under either policy. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_invariantBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (ourInvariantBianchiRow policy).1 = 0 := by
  rw [show (ourInvariantBianchiRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) by rfl,
    ourFourCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourFourCoordinateInvariantTraceOrderCorrection_ourBianchi_zero]

/-- The four-coordinate correction retains the actual Reynolds-averaged
on-shell EOM member. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_invariantEOM_zero :
    ourFourCoordinateInvariantTraceOrderCorrection ourInvariantEOMRow.1 = 0 := by
  rw [show ourInvariantEOMRow.1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator .onShell
          (Finsupp.single ourFieldSevenEOMGenerator 1)) by rfl,
    ourFourCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourFourCoordinateInvariantTraceOrderCorrection_ourEOM_zero]

/-- The four-coordinate correction retains every Reynolds-averaged lifted
derivative-free eight-field trace relation. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_invariantLiftedTraceGenerator_zero
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1))) =
      0 := by
  rw [ourFourCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourFourCoordinateInvariantTraceOrderCorrection_liftedTraceGenerator_zero]

#print axioms ourTraceCycleType_relabel
#print axioms ourTwoCycleTraceAxisMultiplicity_relabel
#print axioms ourTraceAnticommutatorBase_twoCycleTraceAxisSignedWeight
#print axioms ourTraceAnticommutatorSwap_twoCycleTraceAxisSignedWeight
#print axioms ourTraceAnticommutatorSplit_twoCycleTraceAxisSignedWeight
#print axioms ourInvariantTwoCycleTraceAxisCoordinate_ourTraceAnticommutator
#print axioms ourFourCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator_zero
#print axioms ourFourCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator_zero
#print axioms source_twoCycleTraceAxisSignedWeight
#print axioms ourIBP_twoCycleTraceAxisSignedWeight
#print axioms ourSecondIBP_twoCycleTraceAxisSignedWeight
#print axioms ourFourCoordinateInvariantTraceOrderCorrection_ourCommutator_zero
#print axioms ourFourCoordinateInvariantTraceOrderCorrection_ourIBP_zero
#print axioms ourFourCoordinateInvariantTraceOrderCorrection_ourSecondIBP_zero
#print axioms ourBianchiBase_twoCycleTraceAxisSignedWeight
#print axioms ourBianchiRotateOne_twoCycleTraceAxisSignedWeight
#print axioms ourBianchiRotateTwo_twoCycleTraceAxisSignedWeight
#print axioms ourFourCoordinateInvariantTraceOrderCorrection_ourBianchi_zero
#print axioms ourEOMZero_twoCycleTraceAxisSignedWeight
#print axioms ourEOMOne_twoCycleTraceAxisSignedWeight
#print axioms ourEOMThree_twoCycleTraceAxisSignedWeight
#print axioms ourFourCoordinateInvariantTraceOrderCorrection_ourEOM_zero
#print axioms ourFourCoordinateInvariantTraceOrderCorrection_liftedTraceGenerator_zero
#print axioms ourFourCoordinateInvariantTraceOrderCorrection_invariantCommutator_zero
#print axioms ourFourCoordinateInvariantTraceOrderCorrection_invariantIBP_zero
#print axioms ourFourCoordinateInvariantTraceOrderCorrection_invariantSecondIBP_zero
#print axioms ourFourCoordinateInvariantTraceOrderCorrection_invariantBianchi_zero
#print axioms ourFourCoordinateInvariantTraceOrderCorrection_invariantEOM_zero
#print axioms ourFourCoordinateInvariantTraceOrderCorrection_invariantLiftedTraceGenerator_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderTraceTopologyRepair
