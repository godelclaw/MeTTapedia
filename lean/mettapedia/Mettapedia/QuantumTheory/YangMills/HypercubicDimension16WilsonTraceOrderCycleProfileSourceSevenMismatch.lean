import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCertificate
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceMismatch
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalRelationBlocks

/-!
# OUR source-seven quotient certificate for physical commutators

This module constructs a second concrete source-seven covariant commutator
whose curvature output has a different field-plane profile from the previously
used incoming pair.  A bounded kernel-checked quotient calculation separates
that pair from the incoming compensator class.  The companion refutation module
uses this certificate to assess OUR present one-class correction.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch

open V14HypercubicFDCensus
open HypercubicRawFDCharacterCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16AntisymmetryQuotient
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationBlocks
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16PhysicalTraceEvaluationMatrices
open HypercubicDimension16PhysicalTraceEvaluationInvariant
open HypercubicDimension16TraceEvaluation

/-! ## OUR second concrete source-seven commutator -/

/-- OUR seven-field carrier whose third field and inserted curvature share
the `0,2` plane, while its other fields use the `0,1` plane. -/
abbrev ourSecondaryFieldSevenCommutatorCarrier : RelationCarrier :=
  ⟨(⟨7, by decide⟩ : Fin 9),
    ({ trace := ⟨finRotate 7⟩
       fieldFirst := fun _ => 0
       fieldSecond := fun field => if field = 2 then 2 else 1
       derivativeWord :=
         { ownerAtPosition := fun _ => 0
           axisAtPosition := fun position =>
             if position = 0 then 0 else 2 } } :
      DerivativeAlphaReducedSector 7 2)⟩

/-- OUR valid adjacent derivative pair in the secondary carrier. -/
abbrev ourSecondaryFieldSevenCommutatorSite :
    CovariantCommutatorSite ourSecondaryFieldSevenCommutatorCarrier where
  field := ⟨0, by decide⟩
  outer := ⟨0, by
    norm_num [ourSecondaryFieldSevenCommutatorCarrier,
      dimension16DerivativeCount]⟩
  inner := ⟨1, by
    norm_num [ourSecondaryFieldSevenCommutatorCarrier,
      dimension16DerivativeCount]⟩
  outer_lt_inner := by decide
  owner_outer := rfl
  owner_inner := rfl
  no_same_owner_between := by
    intro position houter hinner
    exfalso
    change 0 < position.1 at houter
    change position.1 < 1 at hinner
    omega

/-- OUR physical-relation generator induced by the secondary commutator. -/
def ourSecondaryFieldSevenCommutatorGenerator
    (policy : PhysicalRelationPolicy) : PhysicalRelationGenerator policy :=
  .covariantCommutator ourSecondaryFieldSevenCommutatorCarrier
    ourSecondaryFieldSevenCommutatorSite

/-- OUR labeled sector of one secondary curvature insertion. -/
abbrev ourSecondaryCommutatorInsertionLabeledSector
    (side : CurvatureInsertionSide) : LabeledLocalWordSector 8 0 :=
  orientedLocalSectorEquivLabeled 8 0
    (normalizedSectorData
      (insertCurvatureCarrier ourSecondaryFieldSevenCommutatorSite side).2)

/-- OUR common trace before the distinguished field is moved. -/
def ourSecondaryBeforeTrace : Equiv.Perm (Fin 8) where
  toFun := fun field => Fin.ofNat 8
    (#[1, 2, 3, 4, 5, 6, 7, 0].getD field.1 0)
  invFun := fun field => Fin.ofNat 8
    (#[7, 0, 1, 2, 3, 4, 5, 6].getD field.1 0)
  left_inv := by intro field; fin_cases field <;> decide +kernel
  right_inv := by intro field; fin_cases field <;> decide +kernel

/-- OUR common trace after the distinguished field is moved. -/
def ourSecondaryAfterTrace : Equiv.Perm (Fin 8) where
  toFun := fun field => Fin.ofNat 8
    (#[7, 2, 3, 4, 5, 6, 0, 1].getD field.1 0)
  invFun := fun field => Fin.ofNat 8
    (#[6, 7, 1, 2, 3, 4, 5, 0].getD field.1 0)
  left_inv := by intro field; fin_cases field <;> decide +kernel
  right_inv := by intro field; fin_cases field <;> decide +kernel

/-- OUR derivative-free plane decoration of the secondary pair. -/
def ourSecondaryDecoration : LocalWordDecoration 8 0 :=
  ⟨fun field =>
      { plane := Fin.ofNat 6
          (#[0, 0, 1, 0, 0, 0, 0, 1].getD field.1 0)
        derivativeCount := 0
        derivativeAxis := Fin.elim0 }, by simp⟩

/-- OUR literal before-insertion source for the secondary pair. -/
def ourSecondaryBeforeSource : LabeledLocalWordSector 8 0 where
  trace := ourSecondaryBeforeTrace
  decoration := ourSecondaryDecoration

/-- OUR literal after-insertion source for the secondary pair. -/
def ourSecondaryAfterSource : LabeledLocalWordSector 8 0 where
  trace := ourSecondaryAfterTrace
  decoration := ourSecondaryDecoration

/-- At derivative degree zero, equality of oriented planes determines a
local field letter. -/
theorem our_secondaryLocalFieldLetter_zero_ext (left right : LocalFieldLetter 0)
    (hplane : left.plane = right.plane) : left = right := by
  rcases left with ⟨leftPlane, leftCount, leftAxis⟩
  rcases right with ⟨rightPlane, rightCount, rightAxis⟩
  dsimp at hplane
  subst rightPlane
  have hleft : leftCount = 0 := Fin.eq_zero leftCount
  have hright : rightCount = 0 := Fin.eq_zero rightCount
  subst leftCount
  subst rightCount
  have haxis : leftAxis = rightAxis := by
    funext position
    exact Fin.elim0 position
  subst rightAxis
  rfl

/-- OUR identification of the secondary before source with its actual
curvature insertion. -/
theorem ourSecondaryBeforeSource_eq_insertion :
    ourSecondaryBeforeSource =
      ourSecondaryCommutatorInsertionLabeledSector CurvatureInsertionSide.before := by
  apply LabeledLocalWordSector.ext
  · apply Equiv.ext
    intro field
    fin_cases field <;> decide +kernel
  · apply Subtype.ext
    funext field
    apply our_secondaryLocalFieldLetter_zero_ext
    fin_cases field <;> decide +kernel

/-- OUR identification of the secondary after source with its actual
curvature insertion. -/
theorem ourSecondaryAfterSource_eq_insertion :
    ourSecondaryAfterSource =
      ourSecondaryCommutatorInsertionLabeledSector CurvatureInsertionSide.after := by
  apply LabeledLocalWordSector.ext
  · apply Equiv.ext
    intro field
    fin_cases field <;> decide +kernel
  · apply Subtype.ext
    funext field
    apply our_secondaryLocalFieldLetter_zero_ext
    fin_cases field <;> decide +kernel

/-- OUR eight-field exact target of one secondary curvature insertion. -/
abbrev ourSecondaryCommutatorInsertionExactTarget
    (side : CurvatureInsertionSide) : ExactFieldRelabelOrbitCarrier :=
  ⟨ourEightFieldCount,
    Quotient.mk _ (ourSecondaryCommutatorInsertionLabeledSector side)⟩

/-- OUR exact field-indexed literal target of a secondary source. -/
def ourSecondaryLiteralExactTarget
    (source : LabeledLocalWordSector 8 0) : ExactFieldRelabelOrbitCarrier :=
  ⟨ourEightFieldCount, Quotient.mk _ source⟩

/-- OUR before endpoint agrees with its literal secondary source. -/
theorem ourSecondaryCommutatorInsertionExactTarget_before_eq_literal :
    ourSecondaryCommutatorInsertionExactTarget CurvatureInsertionSide.before =
      ourSecondaryLiteralExactTarget ourSecondaryBeforeSource := by
  change
    (⟨ourEightFieldCount,
      Quotient.mk _
        (ourSecondaryCommutatorInsertionLabeledSector CurvatureInsertionSide.before)⟩ :
      ExactFieldRelabelOrbitCarrier) =
    ⟨ourEightFieldCount, Quotient.mk _ ourSecondaryBeforeSource⟩
  exact congrArg
    (fun source : LabeledLocalWordSector 8 0 =>
      (⟨ourEightFieldCount, Quotient.mk _ source⟩ :
        ExactFieldRelabelOrbitCarrier))
    ourSecondaryBeforeSource_eq_insertion.symm

/-- OUR after endpoint agrees with its literal secondary source. -/
theorem ourSecondaryCommutatorInsertionExactTarget_after_eq_literal :
    ourSecondaryCommutatorInsertionExactTarget CurvatureInsertionSide.after =
      ourSecondaryLiteralExactTarget ourSecondaryAfterSource := by
  change
    (⟨ourEightFieldCount,
      Quotient.mk _
        (ourSecondaryCommutatorInsertionLabeledSector CurvatureInsertionSide.after)⟩ :
      ExactFieldRelabelOrbitCarrier) =
    ⟨ourEightFieldCount, Quotient.mk _ ourSecondaryAfterSource⟩
  exact congrArg
    (fun source : LabeledLocalWordSector 8 0 =>
      (⟨ourEightFieldCount, Quotient.mk _ source⟩ :
        ExactFieldRelabelOrbitCarrier))
    ourSecondaryAfterSource_eq_insertion.symm

/-- OUR field-indexed description of each secondary curvature insertion. -/
theorem exactFieldRelabelOrbitOfOriented_ourSecondaryCommutatorInsertion
    (side : CurvatureInsertionSide) :
    exactFieldRelabelOrbitOfOriented
        (exactNormalizedSectorData
          (insertCurvatureCarrier ourSecondaryFieldSevenCommutatorSite side)) =
      ourSecondaryCommutatorInsertionExactTarget side := by
  rfl

/-- OUR orientation sign of the secondary before-insertion target. -/
theorem ourSecondaryCommutator_before_orientationCoefficient :
    fieldAxisOrientationCoefficient
        (sectorFieldAxisAssignment
          (insertCurvatureCarrier ourSecondaryFieldSevenCommutatorSite
            CurvatureInsertionSide.before).2) = 1 := by
  decide +kernel

/-- OUR orientation sign of the secondary after-insertion target. -/
theorem ourSecondaryCommutator_after_orientationCoefficient :
    fieldAxisOrientationCoefficient
        (sectorFieldAxisAssignment
          (insertCurvatureCarrier ourSecondaryFieldSevenCommutatorSite
            CurvatureInsertionSide.after).2) = 1 := by
  decide +kernel

/-- OUR exact field-relabel image of an exact contextual basis vector. -/
theorem our_secondaryNormalizeExactContextualBasis_fieldRelabel
    (carrier : RelationCarrier) :
    normalizeExactFieldRelabel (normalizeExactContextualBasis carrier) =
      Finsupp.single
        (exactFieldRelabelOrbitOfOriented
          (exactNormalizedSectorData carrier))
        (fieldAxisOrientationCoefficient
          (sectorFieldAxisAssignment carrier.2)) := by
  simp [normalizeExactContextualBasis,
    normalizeExactFieldRelabelBasis]

/-- OUR exact eight-field component of the secondary physical commutator
column. -/
theorem orbitPhysicalRelationOperator_ourSecondaryCommutator_fieldEight
    (policy : PhysicalRelationPolicy) :
    orbitFieldFilter (fun fieldCount => fieldCount.1 = 8)
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
      -Finsupp.single
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
    ourSecondaryCommutator_before_orientationCoefficient,
    ourSecondaryCommutator_after_orientationCoefficient]
  have hsource :
      (exactFieldRelabelOrbitOfOriented
          (exactNormalizedSectorData ourSecondaryFieldSevenCommutatorCarrier)).1.1 ≠ 8 := by
    change 7 ≠ 8
    norm_num
  simp [orbitFieldFilter, ourSecondaryCommutatorInsertionExactTarget,
    ourEightFieldCount, hsource]
  rw [Finsupp.filter_single_of_neg]
  change 7 ≠ 8
  norm_num

/-- OUR literal-source form of the secondary eight-field component. -/
theorem orbitPhysicalRelationOperator_ourSecondaryCommutator_fieldEight_literal
    (policy : PhysicalRelationPolicy) :
    orbitFieldFilter (fun fieldCount => fieldCount.1 = 8)
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
      -Finsupp.single
          (ourSecondaryLiteralExactTarget ourSecondaryBeforeSource) 1 +
        Finsupp.single
          (ourSecondaryLiteralExactTarget ourSecondaryAfterSource) 1 := by
  rw [orbitPhysicalRelationOperator_ourSecondaryCommutator_fieldEight]
  rw [ourSecondaryCommutatorInsertionExactTarget_before_eq_literal,
    ourSecondaryCommutatorInsertionExactTarget_after_eq_literal]

/-! ## OUR bounded trace-functional separation -/

/-- OUR reflection block for the secondary sources at the selected exact
evaluation assignment. -/
def ourSecondarySourceReflectionBlock
    (source : LabeledLocalWordSector 8 0) (permutation : Fin 24) : ℚ :=
  ∑ reflectionMask : Fin 16,
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    source.tensorSign h *
      labeledPlaneTraceEvaluation (encodedEvaluationMatrixAt ⟨2, by decide⟩)
        (source.hypercubicAct h)

/-- OUR one-reflection representative for a secondary permutation block. -/
def ourSecondarySourcePermutationContribution
    (source : LabeledLocalWordSector 8 0) (permutation : Fin 24) : ℚ :=
  let h := decodedHypercubicCharacterElement permutation 0
  source.tensorSign h *
    labeledPlaneTraceEvaluation (encodedEvaluationMatrixAt ⟨2, by decide⟩)
      (source.hypercubicAct h)

/-- OUR compact 24-entry table for the secondary before source. -/
def ourSecondaryExpectedBeforePermutationContribution : Fin 24 → ℚ :=
  fun _ => 2

/-- OUR compact 24-entry table for the secondary after source. -/
def ourSecondaryExpectedAfterPermutationContribution : Fin 24 → ℚ
  | 13 | 15 | 16 | 17 | 19 | 21 | 22 | 23 => -2
  | _ => 2

/-- OUR secondary before source is reflection-invariant at fixed unsigned
permutation. -/
theorem ourSecondaryBefore_action_reflection_invariant
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    ourSecondaryBeforeSource.hypercubicAct
        (decodedHypercubicCharacterElement permutation reflectionMask) =
      ourSecondaryBeforeSource.hypercubicAct
        (decodedHypercubicCharacterElement permutation 0) := by
  rfl

/- OUR kernel-checked reflection-sign cancellation for the secondary before
source. -/
set_option maxHeartbeats 2000000 in
theorem ourSecondaryBefore_tensorSign_reflection_invariant
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    ourSecondaryBeforeSource.tensorSign
        (decodedHypercubicCharacterElement permutation reflectionMask) =
      ourSecondaryBeforeSource.tensorSign
        (decodedHypercubicCharacterElement permutation 0) := by
  set_option maxRecDepth 100000 in
    fin_cases permutation <;> fin_cases reflectionMask <;> decide +kernel

/-- OUR factorization of a secondary-before reflection summand. -/
theorem ourSecondaryBefore_reflection_term
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    ourSecondaryBeforeSource.tensorSign h *
      labeledPlaneTraceEvaluation (encodedEvaluationMatrixAt ⟨2, by decide⟩)
        (ourSecondaryBeforeSource.hypercubicAct h) =
      ourSecondarySourcePermutationContribution ourSecondaryBeforeSource permutation := by
  dsimp [ourSecondarySourcePermutationContribution]
  rw [ourSecondaryBefore_tensorSign_reflection_invariant]
  rw [ourSecondaryBefore_action_reflection_invariant]

/-- OUR factorization of one secondary-before reflection block. -/
theorem ourSecondaryBefore_block_factor
    (permutation : Fin 24) :
    ourSecondarySourceReflectionBlock ourSecondaryBeforeSource permutation =
      16 * ourSecondarySourcePermutationContribution
        ourSecondaryBeforeSource permutation := by
  unfold ourSecondarySourceReflectionBlock
  simp_rw [ourSecondaryBefore_reflection_term]
  norm_num

/- OUR kernel-checked 24-entry table for the secondary before source. -/
set_option maxHeartbeats 3000000 in
theorem ourSecondaryBefore_permutation_table
    (permutation : Fin 24) :
    ourSecondarySourcePermutationContribution ourSecondaryBeforeSource permutation =
      ourSecondaryExpectedBeforePermutationContribution permutation := by
  set_option maxRecDepth 100000 in
    fin_cases permutation <;> decide +kernel

/-- OUR secondary after source is reflection-invariant at fixed unsigned
permutation. -/
theorem ourSecondaryAfter_action_reflection_invariant
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    ourSecondaryAfterSource.hypercubicAct
        (decodedHypercubicCharacterElement permutation reflectionMask) =
      ourSecondaryAfterSource.hypercubicAct
        (decodedHypercubicCharacterElement permutation 0) := by
  rfl

/- OUR kernel-checked reflection-sign cancellation for the secondary after
source. -/
set_option maxHeartbeats 2000000 in
theorem ourSecondaryAfter_tensorSign_reflection_invariant
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    ourSecondaryAfterSource.tensorSign
        (decodedHypercubicCharacterElement permutation reflectionMask) =
      ourSecondaryAfterSource.tensorSign
        (decodedHypercubicCharacterElement permutation 0) := by
  set_option maxRecDepth 100000 in
    fin_cases permutation <;> fin_cases reflectionMask <;> decide +kernel

/-- OUR factorization of a secondary-after reflection summand. -/
theorem ourSecondaryAfter_reflection_term
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    ourSecondaryAfterSource.tensorSign h *
      labeledPlaneTraceEvaluation (encodedEvaluationMatrixAt ⟨2, by decide⟩)
        (ourSecondaryAfterSource.hypercubicAct h) =
      ourSecondarySourcePermutationContribution ourSecondaryAfterSource permutation := by
  dsimp [ourSecondarySourcePermutationContribution]
  rw [ourSecondaryAfter_tensorSign_reflection_invariant]
  rw [ourSecondaryAfter_action_reflection_invariant]

/-- OUR factorization of one secondary-after reflection block. -/
theorem ourSecondaryAfter_block_factor
    (permutation : Fin 24) :
    ourSecondarySourceReflectionBlock ourSecondaryAfterSource permutation =
      16 * ourSecondarySourcePermutationContribution
        ourSecondaryAfterSource permutation := by
  unfold ourSecondarySourceReflectionBlock
  simp_rw [ourSecondaryAfter_reflection_term]
  norm_num

/- OUR kernel-checked 24-entry table for the secondary after source. -/
set_option maxHeartbeats 3000000 in
theorem ourSecondaryAfter_permutation_table
    (permutation : Fin 24) :
    ourSecondarySourcePermutationContribution ourSecondaryAfterSource permutation =
      ourSecondaryExpectedAfterPermutationContribution permutation := by
  set_option maxRecDepth 100000 in
    fin_cases permutation <;> decide +kernel

/-- OUR exact finite sum of the secondary-before compact table. -/
theorem ourSecondaryExpectedBeforePermutationContribution_sum :
    ∑ permutation : Fin 24,
      ourSecondaryExpectedBeforePermutationContribution permutation = 48 := by
  decide +kernel

/-- OUR exact finite sum of the secondary-after compact table. -/
theorem ourSecondaryExpectedAfterPermutationContribution_sum :
    ∑ permutation : Fin 24,
      ourSecondaryExpectedAfterPermutationContribution permutation = 16 := by
  decide +kernel

/-- OUR full Reynolds value of a secondary literal source. -/
def ourSecondarySourceReynoldsTraceValue
    (source : LabeledLocalWordSector 8 0) : ℚ :=
  (1 / 384 : ℚ) * ∑ h : Hypercubic4,
    source.tensorSign h *
      labeledPlaneTraceEvaluation (encodedEvaluationMatrixAt ⟨2, by decide⟩)
        (source.hypercubicAct h)

/-- OUR decomposition of a secondary Reynolds value into its 24 bounded
reflection blocks. -/
theorem ourSecondarySourceReynoldsTraceValue_blocks
    (source : LabeledLocalWordSector 8 0) :
    ourSecondarySourceReynoldsTraceValue source =
      (1 / 384 : ℚ) * ∑ permutation : Fin 24,
        ourSecondarySourceReflectionBlock source permutation := by
  unfold ourSecondarySourceReynoldsTraceValue
  let summand : Hypercubic4 → ℚ := fun h =>
    source.tensorSign h *
      labeledPlaneTraceEvaluation (encodedEvaluationMatrixAt ⟨2, by decide⟩)
        (source.hypercubicAct h)
  change (1 / 384 : ℚ) * ∑ h : Hypercubic4, summand h = _
  calc
    (1 / 384 : ℚ) * ∑ h : Hypercubic4, summand h =
        (1 / 384 : ℚ) * ∑ code : Fin 24 × Fin 16,
          summand (hypercubicCharacterCodeEquiv code) := by
      rw [Equiv.sum_comp hypercubicCharacterCodeEquiv summand]
    _ = (1 / 384 : ℚ) * ∑ permutation : Fin 24,
        ourSecondarySourceReflectionBlock source permutation := by
      simp [summand, hypercubicCharacterCodeEquiv,
        ourSecondarySourceReflectionBlock, Fintype.sum_prod_type]

/-- OUR exact Reynolds value of the secondary before source. -/
theorem ourSecondarySourceReynoldsTraceValue_before :
    ourSecondarySourceReynoldsTraceValue ourSecondaryBeforeSource = 2 := by
  rw [ourSecondarySourceReynoldsTraceValue_blocks ourSecondaryBeforeSource]
  simp_rw [ourSecondaryBefore_block_factor,
    ourSecondaryBefore_permutation_table]
  rw [← Finset.mul_sum,
    ourSecondaryExpectedBeforePermutationContribution_sum]
  norm_num

/-- OUR exact Reynolds value of the secondary after source. -/
theorem ourSecondarySourceReynoldsTraceValue_after :
    ourSecondarySourceReynoldsTraceValue ourSecondaryAfterSource = (2 : ℚ) / 3 := by
  rw [ourSecondarySourceReynoldsTraceValue_blocks ourSecondaryAfterSource]
  simp_rw [ourSecondaryAfter_block_factor,
    ourSecondaryAfter_permutation_table]
  rw [← Finset.mul_sum,
    ourSecondaryExpectedAfterPermutationContribution_sum]
  norm_num

/-- OUR ordinary eight-field signed pair of the secondary commutator. -/
def ourSecondaryCommutatorVector : FieldEightOrbitSpace :=
  -Finsupp.single (Quotient.mk _ ourSecondaryBeforeSource) 1 +
    Finsupp.single (Quotient.mk _ ourSecondaryAfterSource) 1

/-- OUR exact nonzero value of the selected trace functional on the
secondary signed pair. -/
theorem rawReynoldsTraceEvaluation_ourSecondaryCommutatorVector :
    rawReynoldsTraceEvaluation ⟨2, by decide⟩ ourSecondaryCommutatorVector =
      -(4 : ℚ) / 3 := by
  unfold ourSecondaryCommutatorVector
  simp only [LinearMap.map_add, LinearMap.map_neg]
  rw [rawReynoldsTraceEvaluation_single,
    rawReynoldsTraceEvaluation_single]
  simp only [FieldRelabelOrbitCarrier.tensorSign_mk,
    FieldRelabelOrbitCarrier.hypercubicAct_mk,
    orbitPlaneTraceEvaluation_mk]
  change -ourSecondarySourceReynoldsTraceValue ourSecondaryBeforeSource +
      ourSecondarySourceReynoldsTraceValue ourSecondaryAfterSource = _
  rw [ourSecondarySourceReynoldsTraceValue_before,
    ourSecondarySourceReynoldsTraceValue_after]
  norm_num

/-- OUR secondary signed pair in the ordinary derivative-free trace
quotient. -/
def ourSecondaryCommutatorClass : FieldEightPhysicalTraceQuotient :=
  Submodule.Quotient.mk (Submodule.Quotient.mk ourSecondaryCommutatorVector)

/-- OUR quotient-evaluation formula for the secondary pair. -/
theorem incomingQuotientTraceEvaluation_ourSecondaryCommutator :
    incomingQuotientTraceEvaluation ⟨2, by decide⟩ ourSecondaryCommutatorClass =
      rawReynoldsTraceEvaluation ⟨2, by decide⟩ ourSecondaryCommutatorVector := by
  rfl

/-- OUR secondary pair survives the ordinary derivative-free trace quotient. -/
theorem ourSecondaryCommutatorClass_ne_zero :
    ourSecondaryCommutatorClass ≠ 0 := by
  intro hzero
  have hvalue := incomingQuotientTraceEvaluation_ourSecondaryCommutator
  rw [rawReynoldsTraceEvaluation_ourSecondaryCommutatorVector] at hvalue
  rw [hzero, LinearMap.map_zero] at hvalue
  norm_num at hvalue

/-! ## The selected functional kills the old compensator class -/

/-- OUR compact assignment-two table for the established incoming before
source. -/
def ourIncomingBeforeAtTwoExpectedPermutationContribution : Fin 24 → ℚ
  | 3 | 5 | 9 | 11 | 12 | 14 | 18 | 20 => 2
  | _ => 0

/-- OUR compact assignment-two table for the established incoming after
source. -/
def ourIncomingAfterAtTwoExpectedPermutationContribution : Fin 24 → ℚ
  | 3 | 5 | 9 | 11 | 12 | 14 | 18 | 20 => 2
  | _ => 0

/-- OUR established before source is reflection-invariant at assignment two. -/
theorem ourIncomingBeforeAtTwo_action_reflection_invariant
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    incomingBeforeSource.hypercubicAct
        (decodedHypercubicCharacterElement permutation reflectionMask) =
      incomingBeforeSource.hypercubicAct
        (decodedHypercubicCharacterElement permutation 0) := by
  rfl

/- OUR kernel-checked reflection-sign cancellation for the established
before source at assignment two. -/
set_option maxHeartbeats 2000000 in
theorem ourIncomingBeforeAtTwo_tensorSign_reflection_invariant
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    incomingBeforeSource.tensorSign
        (decodedHypercubicCharacterElement permutation reflectionMask) =
      incomingBeforeSource.tensorSign
        (decodedHypercubicCharacterElement permutation 0) := by
  set_option maxRecDepth 100000 in
    fin_cases permutation <;> fin_cases reflectionMask <;> decide +kernel

/-- OUR factorization of an established-before reflection summand at
assignment two. -/
theorem ourIncomingBeforeAtTwo_reflection_term
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    incomingBeforeSource.tensorSign h *
      labeledPlaneTraceEvaluation (encodedEvaluationMatrixAt ⟨2, by decide⟩)
        (incomingBeforeSource.hypercubicAct h) =
      ourSecondarySourcePermutationContribution incomingBeforeSource permutation := by
  dsimp [ourSecondarySourcePermutationContribution]
  rw [ourIncomingBeforeAtTwo_tensorSign_reflection_invariant]
  rw [ourIncomingBeforeAtTwo_action_reflection_invariant]

/-- OUR assignment-two factorization of one established-before reflection
block. -/
theorem ourIncomingBeforeAtTwo_block_factor
    (permutation : Fin 24) :
    ourSecondarySourceReflectionBlock incomingBeforeSource permutation =
      16 * ourSecondarySourcePermutationContribution incomingBeforeSource permutation := by
  unfold ourSecondarySourceReflectionBlock
  simp_rw [ourIncomingBeforeAtTwo_reflection_term]
  norm_num

/- OUR kernel-checked 24-entry assignment-two table for the established
before source. -/
set_option maxHeartbeats 3000000 in
theorem ourIncomingBeforeAtTwo_permutation_table
    (permutation : Fin 24) :
    ourSecondarySourcePermutationContribution incomingBeforeSource permutation =
      ourIncomingBeforeAtTwoExpectedPermutationContribution permutation := by
  set_option maxRecDepth 100000 in
    fin_cases permutation <;> decide +kernel

/-- OUR established after source is reflection-invariant at assignment two. -/
theorem ourIncomingAfterAtTwo_action_reflection_invariant
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    incomingAfterSource.hypercubicAct
        (decodedHypercubicCharacterElement permutation reflectionMask) =
      incomingAfterSource.hypercubicAct
        (decodedHypercubicCharacterElement permutation 0) := by
  rfl

/- OUR kernel-checked reflection-sign cancellation for the established after
source at assignment two. -/
set_option maxHeartbeats 2000000 in
theorem ourIncomingAfterAtTwo_tensorSign_reflection_invariant
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    incomingAfterSource.tensorSign
        (decodedHypercubicCharacterElement permutation reflectionMask) =
      incomingAfterSource.tensorSign
        (decodedHypercubicCharacterElement permutation 0) := by
  set_option maxRecDepth 100000 in
    fin_cases permutation <;> fin_cases reflectionMask <;> decide +kernel

/-- OUR factorization of an established-after reflection summand at
assignment two. -/
theorem ourIncomingAfterAtTwo_reflection_term
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    incomingAfterSource.tensorSign h *
      labeledPlaneTraceEvaluation (encodedEvaluationMatrixAt ⟨2, by decide⟩)
        (incomingAfterSource.hypercubicAct h) =
      ourSecondarySourcePermutationContribution incomingAfterSource permutation := by
  dsimp [ourSecondarySourcePermutationContribution]
  rw [ourIncomingAfterAtTwo_tensorSign_reflection_invariant]
  rw [ourIncomingAfterAtTwo_action_reflection_invariant]

/-- OUR assignment-two factorization of one established-after reflection
block. -/
theorem ourIncomingAfterAtTwo_block_factor
    (permutation : Fin 24) :
    ourSecondarySourceReflectionBlock incomingAfterSource permutation =
      16 * ourSecondarySourcePermutationContribution incomingAfterSource permutation := by
  unfold ourSecondarySourceReflectionBlock
  simp_rw [ourIncomingAfterAtTwo_reflection_term]
  norm_num

/- OUR kernel-checked 24-entry assignment-two table for the established
after source. -/
set_option maxHeartbeats 3000000 in
theorem ourIncomingAfterAtTwo_permutation_table
    (permutation : Fin 24) :
    ourSecondarySourcePermutationContribution incomingAfterSource permutation =
      ourIncomingAfterAtTwoExpectedPermutationContribution permutation := by
  set_option maxRecDepth 100000 in
    fin_cases permutation <;> decide +kernel

/-- OUR exact finite sum of the established-before assignment-two table. -/
theorem ourIncomingBeforeAtTwoExpectedPermutationContribution_sum :
    ∑ permutation : Fin 24,
      ourIncomingBeforeAtTwoExpectedPermutationContribution permutation = 16 := by
  decide +kernel

/-- OUR exact finite sum of the established-after assignment-two table. -/
theorem ourIncomingAfterAtTwoExpectedPermutationContribution_sum :
    ∑ permutation : Fin 24,
      ourIncomingAfterAtTwoExpectedPermutationContribution permutation = 16 := by
  decide +kernel

/-- OUR exact assignment-two Reynolds value of the established before
source. -/
theorem ourSecondarySourceReynoldsTraceValue_incomingBeforeAtTwo :
    ourSecondarySourceReynoldsTraceValue incomingBeforeSource = (2 : ℚ) / 3 := by
  rw [ourSecondarySourceReynoldsTraceValue_blocks incomingBeforeSource]
  simp_rw [ourIncomingBeforeAtTwo_block_factor,
    ourIncomingBeforeAtTwo_permutation_table]
  rw [← Finset.mul_sum,
    ourIncomingBeforeAtTwoExpectedPermutationContribution_sum]
  norm_num

/-- OUR exact assignment-two Reynolds value of the established after
source. -/
theorem ourSecondarySourceReynoldsTraceValue_incomingAfterAtTwo :
    ourSecondarySourceReynoldsTraceValue incomingAfterSource = (2 : ℚ) / 3 := by
  rw [ourSecondarySourceReynoldsTraceValue_blocks incomingAfterSource]
  simp_rw [ourIncomingAfterAtTwo_block_factor,
    ourIncomingAfterAtTwo_permutation_table]
  rw [← Finset.mul_sum,
    ourIncomingAfterAtTwoExpectedPermutationContribution_sum]
  norm_num

/-- OUR selected quotient functional annihilates the old one-class
compensator direction. -/
theorem rawReynoldsTraceEvaluation_literalIncoming_assignmentTwo :
    rawReynoldsTraceEvaluation ⟨2, by decide⟩ literalIncomingCommutatorVector =
      0 := by
  unfold literalIncomingCommutatorVector
  simp only [LinearMap.map_add, LinearMap.map_neg]
  rw [rawReynoldsTraceEvaluation_single,
    rawReynoldsTraceEvaluation_single]
  simp only [FieldRelabelOrbitCarrier.tensorSign_mk,
    FieldRelabelOrbitCarrier.hypercubicAct_mk,
    orbitPlaneTraceEvaluation_mk]
  change -ourSecondarySourceReynoldsTraceValue incomingBeforeSource +
      ourSecondarySourceReynoldsTraceValue incomingAfterSource = 0
  rw [ourSecondarySourceReynoldsTraceValue_incomingBeforeAtTwo,
    ourSecondarySourceReynoldsTraceValue_incomingAfterAtTwo]
  norm_num

/-- OUR selected quotient functional annihilates the literal trace class
used by every current compensator. -/
theorem incomingQuotientTraceEvaluation_literalIncoming_assignmentTwo :
    incomingQuotientTraceEvaluation ⟨2, by decide⟩ literalIncomingCommutatorClass =
      0 := by
  change rawReynoldsTraceEvaluation ⟨2, by decide⟩ literalIncomingCommutatorVector =
    0
  exact rawReynoldsTraceEvaluation_literalIncoming_assignmentTwo

#print axioms orbitPhysicalRelationOperator_ourSecondaryCommutator_fieldEight_literal
#print axioms rawReynoldsTraceEvaluation_ourSecondaryCommutatorVector
#print axioms incomingQuotientTraceEvaluation_literalIncoming_assignmentTwo
#print axioms ourSecondaryCommutatorClass_ne_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch
