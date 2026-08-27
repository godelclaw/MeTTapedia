import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalRelationBlocks
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessSemantics

/-!
# A nonzero cross-sector block of the physical relation operator

The covariant-derivative commutator is not homogeneous in field count.  This
file gives a literal dimension-sixteen witness with seven field strengths and
two derivatives whose curvature insertion has a nonzero image in the
eight-field, zero-derivative orbit sector.  Consequently the honest physical
relation operator is upper bidiagonal, but not block diagonal, in field
count.  An eight-field trace quotient therefore cannot be substituted for
the joint physical quotient without retaining the incoming commutator block.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CovariantCompressionWall

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicRawFDCharacterCensus
open HypercubicDimension16CompressionCensus
open HypercubicDimension16ConjugacyCompression
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16AntisymmetryQuotient
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationBlocks
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16OrbitCharacter
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16TraceOrbitChart
open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitChartCertificate
open HypercubicDimension16TraceOrbitBasis
open HypercubicDimension16PhysicalTraceWitnessTypes
open HypercubicDimension16PhysicalTraceWitnessExecutable
open HypercubicDimension16PhysicalTraceWitnessSemantics

/-! ## Size of the honest invariant target -/

theorem scalarInvariantDimension_sector (fieldIndex : Fin 8) :
    Module.finrank ℚ
        (sectorFieldOrbitInvariantSubmodule (fieldIndex.1 + 1)
          (derivativeCountForFields (fieldIndex.1 + 1))) =
      expectedCompressedInvariantMultiplicity .scalar
        (fieldIndex.1 + 1) := by
  have hdimension := finrank_sectorFieldOrbitInvariantSubmodule
    (fieldIndex.1 + 1) (derivativeCountForFields (fieldIndex.1 + 1))
  have hsum :
      (∑ h : Hypercubic4,
          actualOrbitCharacter h (fieldIndex.1 + 1)
            (derivativeCountForFields (fieldIndex.1 + 1))) =
        encodedCompressionMoment .scalar (fieldIndex.1 + 1) := by
    let summand : Hypercubic4 → ℚ := fun h =>
      actualOrbitCharacter h (fieldIndex.1 + 1)
        (derivativeCountForFields (fieldIndex.1 + 1))
    calc
      (∑ h : Hypercubic4,
          actualOrbitCharacter h (fieldIndex.1 + 1)
            (derivativeCountForFields (fieldIndex.1 + 1))) =
          ∑ code : Fin 24 × Fin 16,
            summand (hypercubicCharacterCodeEquiv code) := by
        exact (Equiv.sum_comp hypercubicCharacterCodeEquiv summand).symm
      _ = encodedCompressionMoment .scalar (fieldIndex.1 + 1) := by
        simp [summand, hypercubicCharacterCodeEquiv,
          encodedCompressionMoment, encodedCompressionReflectionMoment,
          Fintype.sum_prod_type,
          actualOrbitCharacter_eq_compressedSectorCharacter,
          ContractionParity.character]
  have hnormalization :
      (1 / 384 : ℚ) *
          encodedCompressionMoment .scalar (fieldIndex.1 + 1) =
        compressedInvariantMultiplicity .scalar
          (fieldIndex.1 + 1) := by
    unfold compressedInvariantMultiplicity
    ring
  rw [hsum, hnormalization,
    compressedInvariantMultiplicity_certificate .scalar fieldIndex]
      at hdimension
  exact_mod_cast hdimension

/-- The eight nonempty field sectors already require more than 246 million
scalar invariant coordinates before the physical relations are ranked. -/
theorem exactDimension16ScalarInvariantDimension_total :
    (∑ fieldIndex : Fin 8,
      Module.finrank ℚ
        (sectorFieldOrbitInvariantSubmodule (fieldIndex.1 + 1)
          (derivativeCountForFields (fieldIndex.1 + 1)))) =
      246136792 := by
  simp_rw [scalarInvariantDimension_sector]
  decide +kernel

/-! ## A literal seven-field commutator site -/

/-- Seven fields in one trace cycle.  Field zero has plane `23`, field one
has plane `13`, and the remaining fields have plane `01`.  The two derivatives
on field zero carry axes `0,2`, so their curvature plane `02` is new. -/
abbrev fieldSevenCommutatorCarrier : RelationCarrier :=
  ⟨(⟨7, by decide⟩ : Fin 9),
    ({ trace := ⟨finRotate 7⟩
       fieldFirst := fun field =>
         if field = 0 then 2 else if field = 1 then 1 else 0
       fieldSecond := fun field =>
         if field = 0 then 3 else if field = 1 then 3 else 1
       derivativeWord :=
         { ownerAtPosition := fun _ => 0
           axisAtPosition := fun position =>
             if position = 0 then 0 else 2 } } :
      DerivativeAlphaReducedSector 7 2)⟩

abbrev fieldSevenCommutatorSite :
    CovariantCommutatorSite fieldSevenCommutatorCarrier where
  field := ⟨0, by decide⟩
  outer := ⟨0, by
    norm_num [fieldSevenCommutatorCarrier, dimension16DerivativeCount]⟩
  inner := ⟨1, by
    norm_num [fieldSevenCommutatorCarrier, dimension16DerivativeCount]⟩
  outer_lt_inner := by decide
  owner_outer := rfl
  owner_inner := rfl
  no_same_owner_between := by
    intro position houter hinner
    exfalso
    change 0 < position.1 at houter
    change position.1 < 1 at hinner
    omega

@[simp] theorem fieldSevenCommutator_sourceFieldCount :
    fieldSevenCommutatorCarrier.1.1 = 7 := rfl

@[simp] theorem fieldSevenCommutator_successorFieldCount
    (side : CurvatureInsertionSide) :
    (insertCurvatureCarrier fieldSevenCommutatorSite side).1.1 = 8 := rfl

def fieldSevenCommutatorGenerator
    (policy : PhysicalRelationPolicy) : PhysicalRelationGenerator policy :=
  .covariantCommutator fieldSevenCommutatorCarrier
    fieldSevenCommutatorSite

/-! ## Two bounded orbit-chart certificates -/

abbrev commutatorInsertionLabeledSector
    (side : CurvatureInsertionSide) : LabeledLocalWordSector 8 0 :=
  orientedLocalSectorEquivLabeled 8 0
    (normalizedSectorData
      (insertCurvatureCarrier fieldSevenCommutatorSite side).2)

abbrev commutatorInsertionOrbit (side : CurvatureInsertionSide) :
    FieldRelabelOrbitCarrier 8 0 :=
  Quotient.mk _ (commutatorInsertionLabeledSector side)

/-- Fixed-width encoding of the insertion immediately before field zero. -/
abbrev commutatorBeforeSourceCode : Array Nat :=
  #[1, 2, 3, 4, 5, 6, 7, 0,
    7, 0, 1, 2, 3, 4, 5, 6,
    5, 4, 0, 0, 0, 0, 0, 1]

/-- Fixed-width encoding of the insertion immediately after field zero. -/
abbrev commutatorAfterSourceCode : Array Nat :=
  #[7, 2, 3, 4, 5, 6, 0, 1,
    6, 7, 1, 2, 3, 4, 5, 0,
    5, 4, 0, 0, 0, 0, 0, 1]

abbrev commutatorBeforeIndex : PositiveRepresentativeIndex :=
  ⟨10513, by decide⟩

abbrev commutatorAfterIndex : PositiveRepresentativeIndex :=
  ⟨10515, by decide⟩

abbrev commutatorBeforeCoordinate : EncodedOrbitCoordinateWitness where
  coefficient := 1
  representative := 10513
  permutation := 0
  reflection := 0
  renameForward := #[6, 7, 0, 1, 2, 3, 4, 5]
  renameBackward := #[2, 3, 4, 5, 6, 7, 0, 1]

abbrev commutatorAfterCoordinate : EncodedOrbitCoordinateWitness where
  coefficient := 1
  representative := 10515
  permutation := 0
  reflection := 0
  renameForward := #[5, 7, 0, 1, 2, 3, 4, 6]
  renameBackward := #[2, 3, 4, 5, 6, 0, 7, 1]

/-- The generic witness decoder is used here only as a standard labeled-orbit
decoder; kind zero leaves the literal source trace unchanged. -/
abbrev commutatorBeforeWitness : EncodedPhysicalTraceWitness where
  kind := 0
  sourceCode := commutatorBeforeSourceCode
  first := 0
  second := 0
  third := 0
  coordinates := #[commutatorBeforeCoordinate]

abbrev commutatorAfterWitness : EncodedPhysicalTraceWitness where
  kind := 0
  sourceCode := commutatorAfterSourceCode
  first := 0
  second := 0
  third := 0
  coordinates := #[commutatorAfterCoordinate]

theorem commutatorBeforeSourceCode_valid :
    EncodedRepresentativeValid commutatorBeforeSourceCode := by
  decide +kernel

theorem commutatorAfterSourceCode_valid :
    EncodedRepresentativeValid commutatorAfterSourceCode := by
  decide +kernel

theorem commutatorBeforeCoordinate_valid :
    EncodedCoordinateOrbitValid commutatorBeforeWitness 0
      commutatorBeforeCoordinate := by
  decide +kernel

theorem commutatorAfterCoordinate_valid :
    EncodedCoordinateOrbitValid commutatorAfterWitness 0
      commutatorAfterCoordinate := by
  decide +kernel

theorem commutatorBefore_decodedSource :
    decodedPhysicalWitnessSource commutatorBeforeWitness
        commutatorBeforeSourceCode_valid =
      commutatorInsertionLabeledSector CurvatureInsertionSide.before := by
  apply LabeledLocalWordSector.ext
  · apply Equiv.ext
    intro field
    fin_cases field <;> decide +kernel
  · apply Subtype.ext
    funext field
    apply localFieldLetter_zero_ext
    fin_cases field <;> decide +kernel

theorem commutatorAfter_decodedSource :
    decodedPhysicalWitnessSource commutatorAfterWitness
        commutatorAfterSourceCode_valid =
      commutatorInsertionLabeledSector CurvatureInsertionSide.after := by
  apply LabeledLocalWordSector.ext
  · apply Equiv.ext
    intro field
    fin_cases field <;> decide +kernel
  · apply Subtype.ext
    funext field
    apply localFieldLetter_zero_ext
    fin_cases field <;> decide +kernel

/-- The two curvature insertions land in distinct checked chart orbits. -/
theorem commutatorInsertionOrbit_before_eq :
    commutatorInsertionOrbit CurvatureInsertionSide.before =
      positiveRepresentativeTarget commutatorBeforeIndex := by
  change (Quotient.mk _
      (commutatorInsertionLabeledSector CurvatureInsertionSide.before) :
      FieldRelabelOrbitCarrier 8 0) = _
  rw [← commutatorBefore_decodedSource]
  have horbit := decodedPhysicalWitnessTerm_orbit_eq commutatorBeforeWitness
      commutatorBeforeSourceCode_valid (Or.inl rfl) 0
      commutatorBeforeCoordinate commutatorBeforeCoordinate_valid
  have hidentity :
      encodedCoordinateHypercubic commutatorBeforeCoordinate = 1 := by
    apply Hypercubic4.ext <;> intro axis <;> fin_cases axis <;> rfl
  have hindex :
      encodedCoordinateRepresentative commutatorBeforeCoordinate =
        commutatorBeforeIndex := by
    decide +kernel
  rw [hidentity] at horbit
  rw [FieldRelabelOrbitCarrier.hypercubicAct_one] at horbit
  rw [hindex] at horbit
  simpa [decodedPhysicalWitnessTerm] using horbit

theorem commutatorInsertionOrbit_after_eq :
    commutatorInsertionOrbit CurvatureInsertionSide.after =
      positiveRepresentativeTarget commutatorAfterIndex := by
  change (Quotient.mk _
      (commutatorInsertionLabeledSector CurvatureInsertionSide.after) :
      FieldRelabelOrbitCarrier 8 0) = _
  rw [← commutatorAfter_decodedSource]
  have horbit := decodedPhysicalWitnessTerm_orbit_eq commutatorAfterWitness
      commutatorAfterSourceCode_valid (Or.inl rfl) 0
      commutatorAfterCoordinate commutatorAfterCoordinate_valid
  have hidentity :
      encodedCoordinateHypercubic commutatorAfterCoordinate = 1 := by
    apply Hypercubic4.ext <;> intro axis <;> fin_cases axis <;> rfl
  have hindex :
      encodedCoordinateRepresentative commutatorAfterCoordinate =
        commutatorAfterIndex := by
    decide +kernel
  rw [hidentity] at horbit
  rw [FieldRelabelOrbitCarrier.hypercubicAct_one] at horbit
  rw [hindex] at horbit
  simpa [decodedPhysicalWitnessTerm] using horbit

theorem commutatorInsertionOrbits_ne :
    commutatorInsertionOrbit CurvatureInsertionSide.before ≠
      commutatorInsertionOrbit CurvatureInsertionSide.after := by
  rw [commutatorInsertionOrbit_before_eq,
    commutatorInsertionOrbit_after_eq]
  have hseparated := positiveRepresentativeTargets_hypercubic_separated
    (by decide : commutatorBeforeIndex ≠ commutatorAfterIndex) 1
  rw [FieldRelabelOrbitCarrier.hypercubicAct_one] at hseparated
  exact hseparated

abbrev commutatorInsertionExactTarget
    (side : CurvatureInsertionSide) : ExactFieldRelabelOrbitCarrier :=
  ⟨(⟨8, by decide⟩ : Fin 9), commutatorInsertionOrbit side⟩

theorem commutator_before_orientationCoefficient :
    fieldAxisOrientationCoefficient
        (sectorFieldAxisAssignment
          (insertCurvatureCarrier fieldSevenCommutatorSite
            CurvatureInsertionSide.before).2) = 1 := by
  decide +kernel

theorem commutator_after_orientationCoefficient :
    fieldAxisOrientationCoefficient
        (sectorFieldAxisAssignment
          (insertCurvatureCarrier fieldSevenCommutatorSite
            CurvatureInsertionSide.after).2) = 1 := by
  decide +kernel

@[simp] theorem fieldSevenCommutator_swappedFieldCount :
    (swapExactDerivativePositions fieldSevenCommutatorCarrier
      fieldSevenCommutatorSite.outer
      fieldSevenCommutatorSite.inner).1.1 = 7 := rfl

theorem exactFieldRelabelOrbitOfOriented_commutatorInsertion
    (side : CurvatureInsertionSide) :
    exactFieldRelabelOrbitOfOriented
        (exactNormalizedSectorData
          (insertCurvatureCarrier fieldSevenCommutatorSite side)) =
      commutatorInsertionExactTarget side := by
  cases side <;> rfl

theorem normalizeExactContextualBasis_fieldRelabel
    (carrier : RelationCarrier) :
    normalizeExactFieldRelabel (normalizeExactContextualBasis carrier) =
      Finsupp.single
        (exactFieldRelabelOrbitOfOriented
          (exactNormalizedSectorData carrier))
        (fieldAxisOrientationCoefficient
          (sectorFieldAxisAssignment carrier.2)) := by
  simp [normalizeExactContextualBasis,
    normalizeExactFieldRelabelBasis]

/-- After exact contextual normalization and field relabeling, the
eight-field part of the literal commutator column is exactly its two standard
curvature insertions. -/
theorem orbitPhysicalRelationOperator_commutator_fieldEight
    (policy : PhysicalRelationPolicy) :
    orbitFieldFilter (fun fieldCount => fieldCount.1 = 8)
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (fieldSevenCommutatorGenerator policy) 1)) =
      -Finsupp.single
          (commutatorInsertionExactTarget CurvatureInsertionSide.before) 1 +
        Finsupp.single
          (commutatorInsertionExactTarget CurvatureInsertionSide.after) 1 := by
  simp only [orbitPhysicalRelationOperator,
    normalizedPhysicalRelationOperator,
    LinearMap.comp_apply, physicalRelationOperator_single, one_smul,
    fieldSevenCommutatorGenerator, physicalRelationRow,
    covariantCommutatorRow, map_sub, map_add,
    normalizeExactContextual_single]
  simp_rw [normalizeExactContextualBasis_fieldRelabel]
  rw [exactFieldRelabelOrbitOfOriented_commutatorInsertion,
    exactFieldRelabelOrbitOfOriented_commutatorInsertion,
    commutator_before_orientationCoefficient,
    commutator_after_orientationCoefficient]
  have hsource :
      (exactFieldRelabelOrbitOfOriented
          (exactNormalizedSectorData fieldSevenCommutatorCarrier)).1.1 ≠ 8 := by
    change 7 ≠ 8
    norm_num
  simp [orbitFieldFilter, commutatorInsertionExactTarget,
    hsource]
  rw [Finsupp.filter_single_of_neg]
  change 7 ≠ 8
  norm_num

theorem commutatorInsertionExactTargets_ne :
    commutatorInsertionExactTarget CurvatureInsertionSide.before ≠
      commutatorInsertionExactTarget CurvatureInsertionSide.after := by
  intro hequal
  apply commutatorInsertionOrbits_ne
  exact eq_of_heq (PSigma.mk.inj hequal).2

/-- The honest orbit relation operator has a nonzero `7 → 8` block. -/
theorem orbitPhysicalRelationOperator_nonzero_seven_to_eight
    (policy : PhysicalRelationPolicy) :
    orbitFieldFilter (fun fieldCount => fieldCount.1 = 8)
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (fieldSevenCommutatorGenerator policy) 1)) ≠ 0 := by
  rw [orbitPhysicalRelationOperator_commutator_fieldEight]
  intro hzero
  have hcoefficient := congrArg
    (fun value : ExactFieldRelabelOrbitSpace =>
      value (commutatorInsertionExactTarget
        CurvatureInsertionSide.before)) hzero
  have hreverse :
      commutatorInsertionExactTarget CurvatureInsertionSide.after ≠
        commutatorInsertionExactTarget CurvatureInsertionSide.before :=
    commutatorInsertionExactTargets_ne.symm
  simp [hreverse] at hcoefficient

/-- No operator preserving every generator's source field sector can equal
the standard physical relation operator. -/
theorem orbitPhysicalRelationOperator_not_fieldCountBlockDiagonal
    (policy : PhysicalRelationPolicy) :
    ¬ (∀ generator coefficient,
      orbitFieldFilter
          (fun fieldCount =>
            fieldCount = physicalRelationGeneratorSourceFieldCount generator)
          (orbitPhysicalRelationOperator policy
            (Finsupp.single generator coefficient)) =
        orbitPhysicalRelationOperator policy
          (Finsupp.single generator coefficient)) := by
  intro hdiagonal
  have hsource := hdiagonal (fieldSevenCommutatorGenerator policy) 1
  have hsuccessor := congrArg
    (orbitFieldFilter (fun fieldCount => fieldCount.1 = 8)) hsource
  have hleftZero :
      orbitFieldFilter (fun fieldCount => fieldCount.1 = 8)
          (orbitFieldFilter
            (fun fieldCount =>
              fieldCount = physicalRelationGeneratorSourceFieldCount
                (fieldSevenCommutatorGenerator policy))
            (orbitPhysicalRelationOperator policy
              (Finsupp.single (fieldSevenCommutatorGenerator policy) 1))) = 0 := by
    apply Finsupp.ext
    intro target
    by_cases height : target.1.1 = 8
    · have hsourceField :
          target.1 ≠ physicalRelationGeneratorSourceFieldCount
            (fieldSevenCommutatorGenerator policy) := by
        intro hequal
        have hvalue := congrArg Fin.val hequal
        norm_num [physicalRelationGeneratorSourceFieldCount,
          physicalRelationGeneratorSourceCarrier,
          fieldSevenCommutatorGenerator,
          fieldSevenCommutatorCarrier] at hvalue
        omega
      simp [orbitFieldFilter, height, hsourceField]
    · simp [orbitFieldFilter, height]
  rw [hleftZero] at hsuccessor
  exact orbitPhysicalRelationOperator_nonzero_seven_to_eight policy
    hsuccessor.symm

/-! ## The incoming block survives the invariant projection -/

/-- The eight-field component `-F_ab X + X F_ab` of the standard
commutator row. -/
def fieldEightIncomingCommutatorVector : SectorFieldOrbitSpace 8 0 :=
  -Finsupp.single
      (commutatorInsertionOrbit CurvatureInsertionSide.before) 1 +
    Finsupp.single
      (commutatorInsertionOrbit CurvatureInsertionSide.after) 1

def fieldEightIncomingCommutatorReynolds :
    sectorFieldOrbitInvariantSubmodule 8 0 :=
  ⟨sectorFieldOrbitReynolds 8 0 fieldEightIncomingCommutatorVector,
    sectorFieldOrbitReynolds_invariant 8 0 _⟩

theorem fieldEightIncomingCommutatorReynolds_ne_zero :
    fieldEightIncomingCommutatorReynolds ≠ 0 := by
  have hbefore :
      orbitReynoldsVector
          (commutatorInsertionOrbit CurvatureInsertionSide.before) =
        positiveRepresentativeReynoldsVector commutatorBeforeIndex := by
    rw [commutatorInsertionOrbit_before_eq]
    rfl
  have hafter :
      orbitReynoldsVector
          (commutatorInsertionOrbit CurvatureInsertionSide.after) =
        positiveRepresentativeReynoldsVector commutatorAfterIndex := by
    rw [commutatorInsertionOrbit_after_eq]
    rfl
  have hdecompose :
      fieldEightIncomingCommutatorReynolds =
        -orbitReynoldsVector
            (commutatorInsertionOrbit CurvatureInsertionSide.before) +
          orbitReynoldsVector
            (commutatorInsertionOrbit CurvatureInsertionSide.after) := by
    apply Subtype.ext
    simp [fieldEightIncomingCommutatorReynolds,
      fieldEightIncomingCommutatorVector, orbitReynoldsVector,
      map_add, map_neg]
  intro hzero
  have hvalue := congrArg
    (fun value : sectorFieldOrbitInvariantSubmodule 8 0 =>
      (value : FieldEightOrbitSpace)
        (positiveRepresentativeTarget commutatorBeforeIndex)) hzero
  rw [hdecompose, hbefore, hafter] at hvalue
  change
    -((positiveRepresentativeReynoldsVector commutatorBeforeIndex :
        FieldEightOrbitSpace)
          (positiveRepresentativeTarget commutatorBeforeIndex)) +
      (positiveRepresentativeReynoldsVector commutatorAfterIndex :
        FieldEightOrbitSpace)
          (positiveRepresentativeTarget commutatorBeforeIndex) = 0 at hvalue
  rw [
    positiveRepresentativeReynoldsVector_apply_ne
      commutatorAfterIndex commutatorBeforeIndex (by decide),
    add_zero] at hvalue
  exact positiveRepresentativeReynoldsVector_apply_self_ne_zero
    commutatorBeforeIndex (neg_eq_zero.mp hvalue)

end HypercubicDimension16CovariantCompressionWall
end YangMills
end QuantumTheory
end Mettapedia
