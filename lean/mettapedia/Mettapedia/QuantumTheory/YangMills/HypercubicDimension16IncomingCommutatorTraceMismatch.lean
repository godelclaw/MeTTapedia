import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCertificate
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalRelationBlocks

/-!
# OUR local realization of the incoming commutator trace mismatch

This module realizes, directly in the lightweight physical relation-operator
layer, the two literal eight-field sources used by
`HypercubicDimension16IncomingCommutatorTraceCertificate`.  It proves that
the eight-field projection of a concrete covariant-commutator generator is
exactly their signed pair.

The paired source has a nonzero class in the isolated ordinary
derivative-free trace quotient.  Thus that isolated quotient does not impose
this incoming relation component and cannot be identified with a joint
quotient that does.  This is an exact semantic comparison; it makes no
joint-rank or conditioning claim.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16IncomingCommutatorTraceMismatch

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

/-! ## OUR concrete cross-sector generator -/

/-- OUR seven-field carrier with two adjacent derivatives on field zero. -/
abbrev ourFieldSevenCommutatorCarrier : RelationCarrier :=
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

/-- OUR valid adjacent derivative pair in the concrete carrier. -/
abbrev ourFieldSevenCommutatorSite :
    CovariantCommutatorSite ourFieldSevenCommutatorCarrier where
  field := ⟨0, by decide⟩
  outer := ⟨0, by
    norm_num [ourFieldSevenCommutatorCarrier, dimension16DerivativeCount]⟩
  inner := ⟨1, by
    norm_num [ourFieldSevenCommutatorCarrier, dimension16DerivativeCount]⟩
  outer_lt_inner := by decide
  owner_outer := rfl
  owner_inner := rfl
  no_same_owner_between := by
    intro position houter hinner
    exfalso
    change 0 < position.1 at houter
    change position.1 < 1 at hinner
    omega

/-- OUR physical-relation generator induced by the concrete commutator site. -/
def ourFieldSevenCommutatorGenerator
    (policy : PhysicalRelationPolicy) : PhysicalRelationGenerator policy :=
  .covariantCommutator ourFieldSevenCommutatorCarrier
    ourFieldSevenCommutatorSite

/-- OUR labeled sector of one curvature insertion. -/
abbrev ourCommutatorInsertionLabeledSector
    (side : CurvatureInsertionSide) : LabeledLocalWordSector 8 0 :=
  orientedLocalSectorEquivLabeled 8 0
    (normalizedSectorData
      (insertCurvatureCarrier ourFieldSevenCommutatorSite side).2)

/-- OUR field-label orbit of one curvature insertion. -/
abbrev ourCommutatorInsertionOrbit (side : CurvatureInsertionSide) :
    FieldRelabelOrbitCarrier 8 0 :=
  Quotient.mk _ (ourCommutatorInsertionLabeledSector side)

/-- OUR shared exact index for the derivative-free eight-field sector. -/
def ourEightFieldCount : Fin 9 := ⟨8, by decide⟩

/-- OUR exact field-indexed target of one curvature insertion. -/
abbrev ourCommutatorInsertionExactTarget
    (side : CurvatureInsertionSide) : ExactFieldRelabelOrbitCarrier :=
  ⟨ourEightFieldCount, ourCommutatorInsertionOrbit side⟩

/-! ## Literal source identification -/

/-- At derivative degree zero, equality of oriented planes determines a
local field letter. -/
theorem our_localFieldLetter_zero_ext (left right : LocalFieldLetter 0)
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

/-- OUR identification of the first literal source with the before-insertion
sector of the concrete covariant commutator. -/
theorem incomingBeforeSource_eq_ourCommutatorInsertion :
    incomingBeforeSource =
      ourCommutatorInsertionLabeledSector CurvatureInsertionSide.before := by
  apply LabeledLocalWordSector.ext
  · apply Equiv.ext
    intro field
    fin_cases field <;> decide +kernel
  · apply Subtype.ext
    funext field
    apply our_localFieldLetter_zero_ext
    fin_cases field <;> decide +kernel

/-- OUR identification of the second literal source with the after-insertion
sector of the concrete covariant commutator. -/
theorem incomingAfterSource_eq_ourCommutatorInsertion :
    incomingAfterSource =
      ourCommutatorInsertionLabeledSector CurvatureInsertionSide.after := by
  apply LabeledLocalWordSector.ext
  · apply Equiv.ext
    intro field
    fin_cases field <;> decide +kernel
  · apply Subtype.ext
    funext field
    apply our_localFieldLetter_zero_ext
    fin_cases field <;> decide +kernel

/-- OUR exact target obtained from one literal eight-field source. -/
def ourLiteralExactTarget
    (source : LabeledLocalWordSector 8 0) : ExactFieldRelabelOrbitCarrier :=
  ⟨ourEightFieldCount, Quotient.mk _ source⟩

/-- OUR endpoint identification for the before-insertion source. -/
theorem ourCommutatorInsertionExactTarget_before_eq_literal :
    ourCommutatorInsertionExactTarget CurvatureInsertionSide.before =
      ourLiteralExactTarget incomingBeforeSource := by
  change
    (⟨ourEightFieldCount,
      Quotient.mk _
        (ourCommutatorInsertionLabeledSector CurvatureInsertionSide.before)⟩ :
      ExactFieldRelabelOrbitCarrier) =
    ⟨ourEightFieldCount, Quotient.mk _ incomingBeforeSource⟩
  exact congrArg
    (fun source : LabeledLocalWordSector 8 0 =>
      (⟨ourEightFieldCount, Quotient.mk _ source⟩ :
        ExactFieldRelabelOrbitCarrier))
    incomingBeforeSource_eq_ourCommutatorInsertion.symm

/-- OUR endpoint identification for the after-insertion source. -/
theorem ourCommutatorInsertionExactTarget_after_eq_literal :
    ourCommutatorInsertionExactTarget CurvatureInsertionSide.after =
      ourLiteralExactTarget incomingAfterSource := by
  change
    (⟨ourEightFieldCount,
      Quotient.mk _
        (ourCommutatorInsertionLabeledSector CurvatureInsertionSide.after)⟩ :
      ExactFieldRelabelOrbitCarrier) =
    ⟨ourEightFieldCount, Quotient.mk _ incomingAfterSource⟩
  exact congrArg
    (fun source : LabeledLocalWordSector 8 0 =>
      (⟨ourEightFieldCount, Quotient.mk _ source⟩ :
        ExactFieldRelabelOrbitCarrier))
    incomingAfterSource_eq_ourCommutatorInsertion.symm

/-- OUR exact field-label description of each curvature insertion. -/
theorem exactFieldRelabelOrbitOfOriented_ourCommutatorInsertion
    (side : CurvatureInsertionSide) :
    exactFieldRelabelOrbitOfOriented
        (exactNormalizedSectorData
          (insertCurvatureCarrier ourFieldSevenCommutatorSite side)) =
      ourCommutatorInsertionExactTarget side := by
  rfl

/-- OUR orientation sign of the before-insertion target. -/
theorem ourCommutator_before_orientationCoefficient :
    fieldAxisOrientationCoefficient
        (sectorFieldAxisAssignment
          (insertCurvatureCarrier ourFieldSevenCommutatorSite
            CurvatureInsertionSide.before).2) = 1 := by
  decide +kernel

/-- OUR orientation sign of the after-insertion target. -/
theorem ourCommutator_after_orientationCoefficient :
    fieldAxisOrientationCoefficient
        (sectorFieldAxisAssignment
          (insertCurvatureCarrier ourFieldSevenCommutatorSite
            CurvatureInsertionSide.after).2) = 1 := by
  decide +kernel

/-- OUR field-relabel image of an exact contextual basis vector. -/
theorem our_normalizeExactContextualBasis_fieldRelabel
    (carrier : RelationCarrier) :
    normalizeExactFieldRelabel (normalizeExactContextualBasis carrier) =
      Finsupp.single
        (exactFieldRelabelOrbitOfOriented
          (exactNormalizedSectorData carrier))
        (fieldAxisOrientationCoefficient
          (sectorFieldAxisAssignment carrier.2)) := by
  simp [normalizeExactContextualBasis,
    normalizeExactFieldRelabelBasis]

/-! ## The actual incoming projection -/

/-- OUR exact computation of the eight-field projection of the concrete
commutator column in the physical relation operator. -/
theorem orbitPhysicalRelationOperator_ourCommutator_fieldEight
    (policy : PhysicalRelationPolicy) :
    orbitFieldFilter (fun fieldCount => fieldCount.1 = 8)
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) =
      -Finsupp.single
          (ourCommutatorInsertionExactTarget CurvatureInsertionSide.before) 1 +
        Finsupp.single
          (ourCommutatorInsertionExactTarget CurvatureInsertionSide.after) 1 := by
  simp only [orbitPhysicalRelationOperator,
    normalizedPhysicalRelationOperator,
    LinearMap.comp_apply, physicalRelationOperator_single, one_smul,
    ourFieldSevenCommutatorGenerator, physicalRelationRow,
    covariantCommutatorRow, map_sub, map_add,
    normalizeExactContextual_single]
  simp_rw [our_normalizeExactContextualBasis_fieldRelabel]
  rw [exactFieldRelabelOrbitOfOriented_ourCommutatorInsertion,
    exactFieldRelabelOrbitOfOriented_ourCommutatorInsertion,
    ourCommutator_before_orientationCoefficient,
    ourCommutator_after_orientationCoefficient]
  have hsource :
      (exactFieldRelabelOrbitOfOriented
          (exactNormalizedSectorData ourFieldSevenCommutatorCarrier)).1.1 ≠ 8 := by
    change 7 ≠ 8
    norm_num
  simp [orbitFieldFilter, ourCommutatorInsertionExactTarget,
    ourEightFieldCount, hsource]
  rw [Finsupp.filter_single_of_neg]
  change 7 ≠ 8
  norm_num

/-- OUR identification of the actual incoming projection with the two literal
sources used by the isolated trace-functional certificate. -/
theorem orbitPhysicalRelationOperator_ourCommutator_fieldEight_literal
    (policy : PhysicalRelationPolicy) :
    orbitFieldFilter (fun fieldCount => fieldCount.1 = 8)
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) =
      -Finsupp.single
          (ourLiteralExactTarget incomingBeforeSource) 1 +
        Finsupp.single
          (ourLiteralExactTarget incomingAfterSource) 1 := by
  rw [orbitPhysicalRelationOperator_ourCommutator_fieldEight]
  rw [ourCommutatorInsertionExactTarget_before_eq_literal,
    ourCommutatorInsertionExactTarget_after_eq_literal]

/-- OUR certified mismatch: the literal signed pair supplied by the actual
incoming projection survives the isolated ordinary derivative-free trace
quotient. -/
theorem actualIncomingLiteralTraceClass_ne_zero :
    literalIncomingCommutatorClass ≠ 0 :=
  literalIncomingCommutatorClass_ne_zero

#print axioms orbitPhysicalRelationOperator_ourCommutator_fieldEight
#print axioms orbitPhysicalRelationOperator_ourCommutator_fieldEight_literal
#print axioms actualIncomingLiteralTraceClass_ne_zero

end HypercubicDimension16IncomingCommutatorTraceMismatch
end YangMills
end QuantumTheory
end Mettapedia
