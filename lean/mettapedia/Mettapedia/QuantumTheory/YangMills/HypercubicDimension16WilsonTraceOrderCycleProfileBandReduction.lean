import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileRepair
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalRelationBlocks

/-!
# OUR two-band reduction for the cycle-profile correction

OUR repaired trace-order coordinate can read only the seven-field component
after signed Reynolds averaging and the eight-field trace component.  Standard
physical relation rows stay in their source field sector, apart from a
covariant-commutator insertion which reaches only the successor sector.  This
module combines those facts: every arbitrary physical generator sourced below
six fields is therefore already invisible to OUR correction.

This is a support reduction, not a complete relation census or a descent
theorem.  The remaining possible source bands are six, seven, and eight.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileBandReduction

open HypercubicRawFDDimension16Census
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationBlocks
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair

/-- The only full-carrier sectors which OUR repaired coordinate can observe. -/
def ourCycleProfileObservableFieldBand (fieldCount : Fin 9) : Prop :=
  fieldCount = ourSevenFieldCount ∨ fieldCount = ourEightFieldCount

instance : DecidablePred ourCycleProfileObservableFieldBand := by
  intro fieldCount
  unfold ourCycleProfileObservableFieldBand
  infer_instance

/-- OUR two-band projection ignores no seven- or eight-field coordinates. -/
theorem exactFieldSevenEightProjection_observableFieldBand_filter
    (value : ExactFieldRelabelOrbitSpace) :
    exactFieldSevenEightProjection
      (orbitFieldFilter ourCycleProfileObservableFieldBand value) =
      exactFieldSevenEightProjection value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp [hleft, hright]
  | single target coefficient =>
      rcases target with ⟨fieldCount, orbit⟩
      fin_cases fieldCount <;>
        simp [orbitFieldFilter, ourCycleProfileObservableFieldBand,
          exactFieldSevenEightProjection,
          exactFieldSevenEightProjectionBasis,
          ourSevenFieldCount, ourEightFieldCount]

/-- A vector with no seven- or eight-field projection is killed by OUR full
cycle-profile correction. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_zero_of_twoBandProjection_zero
    (value : ExactFieldRelabelOrbitSpace)
    (hprojection : exactFieldSevenEightProjection value = 0) :
    ourCycleProfileInvariantTraceOrderCorrection value = 0 := by
  have hseven : exactFieldSevenProjection
      (exactFieldOrbitReynolds value) = 0 := by
    rw [exactFieldSevenProjection_exactFieldOrbitReynolds]
    have hraw : exactFieldSevenProjection value = 0 := by
      change (exactFieldSevenEightProjection value).1 = 0
      simp [hprojection]
    rw [hraw, map_zero]
  have height : exactFieldEightTraceProjection value = 0 := by
    change exactFieldEightTraceClassMap
      (exactFieldEightProjection value) = 0
    have hraw : exactFieldEightProjection value = 0 := by
      rw [← exactFieldSevenEightProjection_snd_eq_fieldEightProjection]
      simp [hprojection]
    rw [hraw, map_zero]
  exact ourCycleProfileInvariantTraceOrderCorrection_zero_of_projections_zero
    value hseven height

/-- OUR correction is supported on the two observable field bands. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_observableFieldBand_filter
    (value : ExactFieldRelabelOrbitSpace) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitFieldFilter ourCycleProfileObservableFieldBand value) =
      ourCycleProfileInvariantTraceOrderCorrection value := by
  let residual : ExactFieldRelabelOrbitSpace :=
    value - orbitFieldFilter ourCycleProfileObservableFieldBand value
  have hprojection : exactFieldSevenEightProjection residual = 0 := by
    dsimp [residual]
    rw [map_sub,
      exactFieldSevenEightProjection_observableFieldBand_filter]
    simp
  have hzero : ourCycleProfileInvariantTraceOrderCorrection residual = 0 :=
    ourCycleProfileInvariantTraceOrderCorrection_zero_of_twoBandProjection_zero
      residual hprojection
  calc
    ourCycleProfileInvariantTraceOrderCorrection
        (orbitFieldFilter ourCycleProfileObservableFieldBand value) =
        ourCycleProfileInvariantTraceOrderCorrection
          (orbitFieldFilter ourCycleProfileObservableFieldBand value) + 0 :=
      (add_zero _).symm
    _ = ourCycleProfileInvariantTraceOrderCorrection
          (orbitFieldFilter ourCycleProfileObservableFieldBand value) +
        ourCycleProfileInvariantTraceOrderCorrection residual := by rw [hzero]
    _ = ourCycleProfileInvariantTraceOrderCorrection
          (orbitFieldFilter ourCycleProfileObservableFieldBand value + residual) :=
      (map_add _ _ _).symm
    _ = ourCycleProfileInvariantTraceOrderCorrection value := by
      congr 1
      dsimp [residual]
      abel

/-- The source-plus-successor field band misses both observable sectors
exactly when the source has fewer than six field strengths. -/
theorem sourceSuccessorBand_misses_observableBands_iff
    (source : Fin 9) :
    (¬ InSourceOrSuccessorFieldSector source ourSevenFieldCount) ∧
      (¬ InSourceOrSuccessorFieldSector source ourEightFieldCount) ↔
      source.1 < 6 := by
  fin_cases source <;> decide

/-- Any physical relation column whose source has fewer than six field
strengths is invisible to OUR cycle-profile correction.  This includes every
arbitrary carrier in those source sectors; no representative enumeration is
being used. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_lt_six
    (policy : PhysicalRelationPolicy)
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ)
    (hsource : (physicalRelationGeneratorSourceFieldCount generator).1 < 6) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient)) = 0 := by
  have hmiss :
      (¬ InSourceOrSuccessorFieldSector
        (physicalRelationGeneratorSourceFieldCount generator) ourSevenFieldCount) ∧
      (¬ InSourceOrSuccessorFieldSector
        (physicalRelationGeneratorSourceFieldCount generator) ourEightFieldCount) :=
    (sourceSuccessorBand_misses_observableBands_iff
      (physicalRelationGeneratorSourceFieldCount generator)).mpr hsource
  have hfilter : orbitFieldFilter ourCycleProfileObservableFieldBand
      (orbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient)) = 0 := by
    apply Finsupp.ext
    intro target
    by_cases htarget : ourCycleProfileObservableFieldBand target.1
    · change (if ourCycleProfileObservableFieldBand target.1 then
          orbitPhysicalRelationOperator policy
            (Finsupp.single generator coefficient) target else 0) = 0
      rw [if_pos htarget]
      apply orbitPhysicalRelationOperator_single_apply_eq_zero_of_outside_field_band
        generator coefficient target
      rcases htarget with hseven | height
      · simpa [hseven] using hmiss.1
      · simpa [height] using hmiss.2
    · simp [orbitFieldFilter, htarget]
  rw [← ourCycleProfileInvariantTraceOrderCorrection_observableFieldBand_filter,
    hfilter]
  simp

/-- Neither observable output band is the six-field source sector. -/
theorem ourCycleProfileObservableFieldBand_ne_six
    (fieldCount : Fin 9)
    (membership : ourCycleProfileObservableFieldBand fieldCount) :
    fieldCount ≠ (6 : Fin 9) := by
  rcases membership with hseven | height
  · rw [hseven]
    intro h
    have hvalue := congrArg Fin.val h
    norm_num [ourSevenFieldCount] at hvalue
  · rw [height]
    intro h
    have hvalue := congrArg Fin.val h
    norm_num [ourEightFieldCount] at hvalue

/-- At source field count six, every noncommutator physical relation column
is already invisible to OUR cycle-profile correction.  The only unclassified
source-six family is therefore the genuinely cross-sector covariant
commutator. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_eq_six_of_not_covariantCommutator
    (policy : PhysicalRelationPolicy)
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ)
    (hsource : physicalRelationGeneratorSourceFieldCount generator = (6 : Fin 9))
    (noncovariant : ∀ (carrier : RelationCarrier)
      (site : CovariantCommutatorSite carrier),
      generator ≠ .covariantCommutator carrier site) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient)) = 0 := by
  have hfilter : orbitFieldFilter ourCycleProfileObservableFieldBand
      (orbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient)) = 0 := by
    apply Finsupp.ext
    intro target
    by_cases htarget : ourCycleProfileObservableFieldBand target.1
    · change (if ourCycleProfileObservableFieldBand target.1 then
          orbitPhysicalRelationOperator policy
            (Finsupp.single generator coefficient) target else 0) = 0
      rw [if_pos htarget]
      apply orbitPhysicalRelationOperator_single_apply_eq_zero_of_outside_source_field_of_not_covariantCommutator
        generator coefficient noncovariant target
      intro htargetSource
      apply ourCycleProfileObservableFieldBand_ne_six target.1 htarget
      calc
        target.1 = physicalRelationGeneratorSourceFieldCount generator := htargetSource
        _ = (6 : Fin 9) := hsource
    · simp [orbitFieldFilter, htarget]
  rw [← ourCycleProfileInvariantTraceOrderCorrection_observableFieldBand_filter,
    hfilter]
  simp

/-- The complete source-six classification for the current correction:
every physical generator is either a covariant commutator or already lies in
the correction kernel.  This does not decide the remaining commutator branch. -/
theorem sourceSixPhysicalRelationGenerator_covariantCommutator_or_profileCorrection_zero
    (policy : PhysicalRelationPolicy)
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ)
    (hsource : physicalRelationGeneratorSourceFieldCount generator = (6 : Fin 9)) :
    (∃ (carrier : RelationCarrier) (site : CovariantCommutatorSite carrier),
      generator = .covariantCommutator carrier site) ∨
      ourCycleProfileInvariantTraceOrderCorrection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single generator coefficient)) = 0 := by
  cases generator with
  | covariantCommutator carrier site =>
      exact Or.inl ⟨carrier, site, rfl⟩
  | antisymmetry carrier slot =>
      exact Or.inr
        (ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_eq_six_of_not_covariantCommutator
          policy (.antisymmetry carrier slot) coefficient hsource
          (by intro carrier' site' hequal; cases hequal))
  | bianchi carrier field position innermost =>
      exact Or.inr
        (ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_eq_six_of_not_covariantCommutator
          policy (.bianchi carrier field position innermost) coefficient hsource
          (by intro carrier' site' hequal; cases hequal))
  | eom enabled carrier field position innermost =>
      exact Or.inr
        (ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_eq_six_of_not_covariantCommutator
          policy (.eom enabled carrier field position innermost) coefficient hsource
          (by intro carrier' site' hequal; cases hequal))
  | integrationByParts carrier position outermost =>
      exact Or.inr
        (ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_eq_six_of_not_covariantCommutator
          policy (.integrationByParts carrier position outermost) coefficient hsource
          (by intro carrier' site' hequal; cases hequal))
  | traceless carrier field singleton =>
      exact Or.inr
        (ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_eq_six_of_not_covariantCommutator
          policy (.traceless carrier field singleton) coefficient hsource
          (by intro carrier' site' hequal; cases hequal))
  | traceAnticommutator carrier site =>
      exact Or.inr
        (ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_eq_six_of_not_covariantCommutator
          policy (.traceAnticommutator carrier site) coefficient hsource
          (by intro carrier' site' hequal; cases hequal))
  | fundamentalTrace carrier site =>
      exact Or.inr
        (ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_eq_six_of_not_covariantCommutator
          policy (.fundamentalTrace carrier site) coefficient hsource
          (by intro carrier' site' hequal; cases hequal))

#print axioms exactFieldSevenEightProjection_observableFieldBand_filter
#print axioms ourCycleProfileInvariantTraceOrderCorrection_zero_of_twoBandProjection_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_observableFieldBand_filter
#print axioms sourceSuccessorBand_misses_observableBands_iff
#print axioms ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_lt_six
#print axioms ourCycleProfileObservableFieldBand_ne_six
#print axioms ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_eq_six_of_not_covariantCommutator
#print axioms sourceSixPhysicalRelationGenerator_covariantCommutator_or_profileCorrection_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileBandReduction
