import KrennCarrierSplitReflection
import KrennComponent57.LeafB0_0
import KrennComponent57.LeafB0_1
import KrennComponent57.LeafB0_2
import KrennComponent57.LeafB0_3
import KrennComponent57.LeafB0_4
import KrennComponent57.LeafB0_5
import KrennComponent57.LeafB0_6
import KrennComponent57.LeafB0_7
import KrennComponent57.LeafB1
import KrennComponent57.LeafB2_0
import KrennComponent57.LeafB2_1
import KrennComponent57.LeafB2_2
import KrennComponent57.LeafB2_3
import KrennComponent57.LeafB2_4
import KrennComponent57.LeafB2_5
import KrennComponent57.LeafB2_6
import KrennComponent57.LeafB2_7
import KrennComponent57.LeafB3
import KrennComponent57.LeafB4_0
import KrennComponent57.LeafB4_1_0
import KrennComponent57.LeafB4_1_1
import KrennComponent57.LeafB4_1_2
import KrennComponent57.LeafB4_1_3
import KrennComponent57.LeafB4_1_4
import KrennComponent57.LeafB4_1_5
import KrennComponent57.LeafB4_1_6
import KrennComponent57.LeafB4_1_7
import KrennComponent57.LeafB4_2_0
import KrennComponent57.LeafB4_2_1
import KrennComponent57.LeafB4_2_2
import KrennComponent57.LeafB4_2_3
import KrennComponent57.LeafB4_2_4
import KrennComponent57.LeafB4_2_5
import KrennComponent57.LeafB4_2_6
import KrennComponent57.LeafB4_2_7
import KrennComponent57.LeafB4_3_0
import KrennComponent57.LeafB4_3_1
import KrennComponent57.LeafB4_3_2
import KrennComponent57.LeafB4_3_3
import KrennComponent57.LeafB4_3_4
import KrennComponent57.LeafB4_3_5
import KrennComponent57.LeafB4_3_6
import KrennComponent57.LeafB4_3_7
import KrennComponent57.LeafB4_4
import KrennComponent57.LeafB4_5
import KrennComponent57.LeafB4_6_0
import KrennComponent57.LeafB4_6_1
import KrennComponent57.LeafB4_6_2
import KrennComponent57.LeafB4_6_3
import KrennComponent57.LeafB4_6_4
import KrennComponent57.LeafB4_6_5
import KrennComponent57.LeafB4_6_6
import KrennComponent57.LeafB4_6_7
import KrennComponent57.LeafB4_7_0
import KrennComponent57.LeafB4_7_1
import KrennComponent57.LeafB4_7_2
import KrennComponent57.LeafB4_7_3
import KrennComponent57.LeafB4_7_4
import KrennComponent57.LeafB4_7_5
import KrennComponent57.LeafB4_7_6
import KrennComponent57.LeafB4_7_7
import KrennComponent57.LeafB5
import KrennComponent57.LeafB6_0
import KrennComponent57.LeafB6_1_0
import KrennComponent57.LeafB6_1_1
import KrennComponent57.LeafB6_1_2
import KrennComponent57.LeafB6_1_3
import KrennComponent57.LeafB6_1_4
import KrennComponent57.LeafB6_1_5
import KrennComponent57.LeafB6_1_6
import KrennComponent57.LeafB6_1_7
import KrennComponent57.LeafB6_2_0
import KrennComponent57.LeafB6_2_1
import KrennComponent57.LeafB6_2_2
import KrennComponent57.LeafB6_2_3
import KrennComponent57.LeafB6_2_4
import KrennComponent57.LeafB6_2_5
import KrennComponent57.LeafB6_2_6
import KrennComponent57.LeafB6_2_7
import KrennComponent57.LeafB6_3_0
import KrennComponent57.LeafB6_3_1
import KrennComponent57.LeafB6_3_2
import KrennComponent57.LeafB6_3_3
import KrennComponent57.LeafB6_3_4
import KrennComponent57.LeafB6_3_5
import KrennComponent57.LeafB6_3_6
import KrennComponent57.LeafB6_3_7
import KrennComponent57.LeafB6_4
import KrennComponent57.LeafB6_5
import KrennComponent57.LeafB6_6_0
import KrennComponent57.LeafB6_6_1
import KrennComponent57.LeafB6_6_2
import KrennComponent57.LeafB6_6_3
import KrennComponent57.LeafB6_6_4
import KrennComponent57.LeafB6_6_5
import KrennComponent57.LeafB6_6_6
import KrennComponent57.LeafB6_6_7
import KrennComponent57.LeafB6_7_0
import KrennComponent57.LeafB6_7_1
import KrennComponent57.LeafB6_7_2
import KrennComponent57.LeafB6_7_3
import KrennComponent57.LeafB6_7_4
import KrennComponent57.LeafB6_7_5
import KrennComponent57.LeafB6_7_6
import KrennComponent57.LeafB6_7_7
import KrennComponent57.LeafB7

namespace Krenn.Component57.Tree

open Krenn.SparseCertificate
open MvPolynomial

def rootEquations : Fin 671 → SparsePoly (Fin 62) :=
  fun index => Krenn.Component57.LeafB0_0.parentEquations ⟨index.val, by omega⟩

def RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 62 → R) : Prop :=
  ∀ index, eval₂Hom (Int.castRingHom R) values
    (rootEquations index).toPoly = 0

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Frozen compatibility and contradiction for terminal chart `b0.0`. -/
theorem leafB00Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 62 → R := values
  let values2 : Fin 62 → R := values1
  apply Krenn.Component57.LeafB0_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨182, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_0.selectedEquations, Krenn.Component57.LeafB0_0.selectedIndices, Krenn.Component57.LeafB0_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b0.1`. -/
theorem leafB01Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := values
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.Component57.LeafB0_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_1.selectedEquations, Krenn.Component57.LeafB0_1.selectedIndices, Krenn.Component57.LeafB0_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨485, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_1.selectedEquations, Krenn.Component57.LeafB0_1.selectedIndices, Krenn.Component57.LeafB0_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_1.selectedEquations, Krenn.Component57.LeafB0_1.selectedIndices, Krenn.Component57.LeafB0_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_1.selectedEquations, Krenn.Component57.LeafB0_1.selectedIndices, Krenn.Component57.LeafB0_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨658, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_1.selectedEquations, Krenn.Component57.LeafB0_1.selectedIndices, Krenn.Component57.LeafB0_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_1.selectedEquations, Krenn.Component57.LeafB0_1.selectedIndices, Krenn.Component57.LeafB0_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_1.selectedEquations, Krenn.Component57.LeafB0_1.selectedIndices, Krenn.Component57.LeafB0_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b0.2`. -/
theorem leafB02Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 62 → R := values
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.Component57.LeafB0_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨182, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_2.selectedEquations, Krenn.Component57.LeafB0_2.selectedIndices, Krenn.Component57.LeafB0_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b0.3`. -/
theorem leafB03Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := values
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component57.LeafB0_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨182, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨185, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨281, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨296, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨437, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨474, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨477, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨485, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_3.selectedEquations, Krenn.Component57.LeafB0_3.selectedIndices, Krenn.Component57.LeafB0_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b0.4`. -/
theorem leafB04Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 62 → R := values
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.Component57.LeafB0_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨182, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_4.selectedEquations, Krenn.Component57.LeafB0_4.selectedIndices, Krenn.Component57.LeafB0_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b0.5`. -/
theorem leafB05Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := values
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.Component57.LeafB0_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨185, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨485, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨489, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨516, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨658, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_5.selectedEquations, Krenn.Component57.LeafB0_5.selectedIndices, Krenn.Component57.LeafB0_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b0.6`. -/
theorem leafB06Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 62 → R := values
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.Component57.LeafB0_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨182, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_6.selectedEquations, Krenn.Component57.LeafB0_6.selectedIndices, Krenn.Component57.LeafB0_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b0.7`. -/
theorem leafB07Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := values
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d1Inverse0
    else if at1 : index.val = 63 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component57.LeafB0_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨77, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨516, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB0_7.selectedEquations, Krenn.Component57.LeafB0_7.selectedIndices, Krenn.Component57.LeafB0_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b1`. -/
theorem leafB1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  apply Krenn.Component57.LeafB1.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB1.selectedEquations, Krenn.Component57.LeafB1.selectedIndices, Krenn.Component57.LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB1.selectedEquations, Krenn.Component57.LeafB1.selectedIndices, Krenn.Component57.LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB1.selectedEquations, Krenn.Component57.LeafB1.selectedIndices, Krenn.Component57.LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB1.selectedEquations, Krenn.Component57.LeafB1.selectedIndices, Krenn.Component57.LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB1.selectedEquations, Krenn.Component57.LeafB1.selectedIndices, Krenn.Component57.LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB1.selectedEquations, Krenn.Component57.LeafB1.selectedIndices, Krenn.Component57.LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB1.selectedEquations, Krenn.Component57.LeafB1.selectedIndices, Krenn.Component57.LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB1.selectedEquations, Krenn.Component57.LeafB1.selectedIndices, Krenn.Component57.LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB1.selectedEquations, Krenn.Component57.LeafB1.selectedIndices, Krenn.Component57.LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB1.selectedEquations, Krenn.Component57.LeafB1.selectedIndices, Krenn.Component57.LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB1.selectedEquations, Krenn.Component57.LeafB1.selectedIndices, Krenn.Component57.LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB1.selectedEquations, Krenn.Component57.LeafB1.selectedIndices, Krenn.Component57.LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB1.selectedEquations, Krenn.Component57.LeafB1.selectedIndices, Krenn.Component57.LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB1.selectedEquations, Krenn.Component57.LeafB1.selectedIndices, Krenn.Component57.LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB1.selectedEquations, Krenn.Component57.LeafB1.selectedIndices, Krenn.Component57.LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB1.selectedEquations, Krenn.Component57.LeafB1.selectedIndices, Krenn.Component57.LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

/-- Frozen compatibility and contradiction for terminal chart `b2.0`. -/
theorem leafB20Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 63 → R := values1
  apply Krenn.Component57.LeafB2_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨182, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_0.selectedEquations, Krenn.Component57.LeafB2_0.selectedIndices, Krenn.Component57.LeafB2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b2.1`. -/
theorem leafB21Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.Component57.LeafB2_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_1.selectedEquations, Krenn.Component57.LeafB2_1.selectedIndices, Krenn.Component57.LeafB2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨485, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_1.selectedEquations, Krenn.Component57.LeafB2_1.selectedIndices, Krenn.Component57.LeafB2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_1.selectedEquations, Krenn.Component57.LeafB2_1.selectedIndices, Krenn.Component57.LeafB2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_1.selectedEquations, Krenn.Component57.LeafB2_1.selectedIndices, Krenn.Component57.LeafB2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨658, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_1.selectedEquations, Krenn.Component57.LeafB2_1.selectedIndices, Krenn.Component57.LeafB2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_1.selectedEquations, Krenn.Component57.LeafB2_1.selectedIndices, Krenn.Component57.LeafB2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_1.selectedEquations, Krenn.Component57.LeafB2_1.selectedIndices, Krenn.Component57.LeafB2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b2.2`. -/
theorem leafB22Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.Component57.LeafB2_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨182, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_2.selectedEquations, Krenn.Component57.LeafB2_2.selectedIndices, Krenn.Component57.LeafB2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b2.3`. -/
theorem leafB23Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component57.LeafB2_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨182, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨185, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨281, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨296, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨437, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨474, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨477, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨485, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_3.selectedEquations, Krenn.Component57.LeafB2_3.selectedIndices, Krenn.Component57.LeafB2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b2.4`. -/
theorem leafB24Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.Component57.LeafB2_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨182, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_4.selectedEquations, Krenn.Component57.LeafB2_4.selectedIndices, Krenn.Component57.LeafB2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b2.5`. -/
theorem leafB25Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.Component57.LeafB2_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨185, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨485, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨489, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨516, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨658, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_5.selectedEquations, Krenn.Component57.LeafB2_5.selectedIndices, Krenn.Component57.LeafB2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b2.6`. -/
theorem leafB26Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.Component57.LeafB2_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨182, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_6.selectedEquations, Krenn.Component57.LeafB2_6.selectedIndices, Krenn.Component57.LeafB2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b2.7`. -/
theorem leafB27Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else if at1 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component57.LeafB2_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨77, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨516, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB2_7.selectedEquations, Krenn.Component57.LeafB2_7.selectedIndices, Krenn.Component57.LeafB2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b3`. -/
theorem leafB3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse1
    else d0Inverse2
  apply Krenn.Component57.LeafB3.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB3.selectedEquations, Krenn.Component57.LeafB3.selectedIndices, Krenn.Component57.LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.0`. -/
theorem leafB40Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 63 → R := values1
  apply Krenn.Component57.LeafB4_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_0.selectedEquations, Krenn.Component57.LeafB4_0.selectedIndices, Krenn.Component57.LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_0.selectedEquations, Krenn.Component57.LeafB4_0.selectedIndices, Krenn.Component57.LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_0.selectedEquations, Krenn.Component57.LeafB4_0.selectedIndices, Krenn.Component57.LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_0.selectedEquations, Krenn.Component57.LeafB4_0.selectedIndices, Krenn.Component57.LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_0.selectedEquations, Krenn.Component57.LeafB4_0.selectedIndices, Krenn.Component57.LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_0.selectedEquations, Krenn.Component57.LeafB4_0.selectedIndices, Krenn.Component57.LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_0.selectedEquations, Krenn.Component57.LeafB4_0.selectedIndices, Krenn.Component57.LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_0.selectedEquations, Krenn.Component57.LeafB4_0.selectedIndices, Krenn.Component57.LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_0.selectedEquations, Krenn.Component57.LeafB4_0.selectedIndices, Krenn.Component57.LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_0.selectedEquations, Krenn.Component57.LeafB4_0.selectedIndices, Krenn.Component57.LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_0.selectedEquations, Krenn.Component57.LeafB4_0.selectedIndices, Krenn.Component57.LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_0.selectedEquations, Krenn.Component57.LeafB4_0.selectedIndices, Krenn.Component57.LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_0.selectedEquations, Krenn.Component57.LeafB4_0.selectedIndices, Krenn.Component57.LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_0.selectedEquations, Krenn.Component57.LeafB4_0.selectedIndices, Krenn.Component57.LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_0.selectedEquations, Krenn.Component57.LeafB4_0.selectedIndices, Krenn.Component57.LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_0.selectedEquations, Krenn.Component57.LeafB4_0.selectedIndices, Krenn.Component57.LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_0.selectedEquations, Krenn.Component57.LeafB4_0.selectedIndices, Krenn.Component57.LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.1.0`. -/
theorem leafB410Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 64 → R := values2
  apply Krenn.Component57.LeafB4_1_0.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_0.selectedEquations, Krenn.Component57.LeafB4_1_0.selectedIndices, Krenn.Component57.LeafB4_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.1.1`. -/
theorem leafB411Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component57.LeafB4_1_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_1.selectedEquations, Krenn.Component57.LeafB4_1_1.selectedIndices, Krenn.Component57.LeafB4_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.1.2`. -/
theorem leafB412Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  apply Krenn.Component57.LeafB4_1_2.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨175, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨256, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨265, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨330, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨339, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨415, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨461, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨491, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨525, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨549, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨550, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨552, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨561, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨621, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨622, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨669, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_2.selectedEquations, Krenn.Component57.LeafB4_1_2.selectedIndices, Krenn.Component57.LeafB4_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.1.3`. -/
theorem leafB413Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB4_1_3.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_3.selectedEquations, Krenn.Component57.LeafB4_1_3.selectedIndices, Krenn.Component57.LeafB4_1_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_3.selectedEquations, Krenn.Component57.LeafB4_1_3.selectedIndices, Krenn.Component57.LeafB4_1_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_3.selectedEquations, Krenn.Component57.LeafB4_1_3.selectedIndices, Krenn.Component57.LeafB4_1_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.1.4`. -/
theorem leafB414Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else d2Inverse0
  apply Krenn.Component57.LeafB4_1_4.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_4.selectedEquations, Krenn.Component57.LeafB4_1_4.selectedIndices, Krenn.Component57.LeafB4_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.1.5`. -/
theorem leafB415Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d2Inverse0
    else d2Inverse2
  apply Krenn.Component57.LeafB4_1_5.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_5.selectedEquations, Krenn.Component57.LeafB4_1_5.selectedIndices, Krenn.Component57.LeafB4_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.1.6`. -/
theorem leafB416Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d2Inverse0
    else d2Inverse1
  apply Krenn.Component57.LeafB4_1_6.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨175, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨256, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨265, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨330, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨339, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨415, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨461, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨491, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨525, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨549, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨550, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨552, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨561, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨621, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨622, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨669, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_6.selectedEquations, Krenn.Component57.LeafB4_1_6.selectedIndices, Krenn.Component57.LeafB4_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.1.7`. -/
theorem leafB417Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d2Inverse0
    else if at1 : index.val = 65 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB4_1_7.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_7.selectedEquations, Krenn.Component57.LeafB4_1_7.selectedIndices, Krenn.Component57.LeafB4_1_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_7.selectedEquations, Krenn.Component57.LeafB4_1_7.selectedIndices, Krenn.Component57.LeafB4_1_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_1_7.selectedEquations, Krenn.Component57.LeafB4_1_7.selectedIndices, Krenn.Component57.LeafB4_1_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.2.0`. -/
theorem leafB420Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 64 → R := values2
  apply Krenn.Component57.LeafB4_2_0.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_0.selectedEquations, Krenn.Component57.LeafB4_2_0.selectedIndices, Krenn.Component57.LeafB4_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.2.1`. -/
theorem leafB421Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component57.LeafB4_2_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨200, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨216, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨219, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨246, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨289, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨358, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨499, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨519, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨524, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨535, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨599, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨600, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨614, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨616, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨617, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨618, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨619, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨620, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨621, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨622, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨624, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨627, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨629, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨630, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨640, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨641, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨642, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨645, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨658, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨659, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨663, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨666, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨667, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨668, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨669, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_1.selectedEquations, Krenn.Component57.LeafB4_2_1.selectedIndices, Krenn.Component57.LeafB4_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.2.2`. -/
theorem leafB422Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  apply Krenn.Component57.LeafB4_2_2.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_2.selectedEquations, Krenn.Component57.LeafB4_2_2.selectedIndices, Krenn.Component57.LeafB4_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_2.selectedEquations, Krenn.Component57.LeafB4_2_2.selectedIndices, Krenn.Component57.LeafB4_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_2.selectedEquations, Krenn.Component57.LeafB4_2_2.selectedIndices, Krenn.Component57.LeafB4_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_2.selectedEquations, Krenn.Component57.LeafB4_2_2.selectedIndices, Krenn.Component57.LeafB4_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_2.selectedEquations, Krenn.Component57.LeafB4_2_2.selectedIndices, Krenn.Component57.LeafB4_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_2.selectedEquations, Krenn.Component57.LeafB4_2_2.selectedIndices, Krenn.Component57.LeafB4_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_2.selectedEquations, Krenn.Component57.LeafB4_2_2.selectedIndices, Krenn.Component57.LeafB4_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_2.selectedEquations, Krenn.Component57.LeafB4_2_2.selectedIndices, Krenn.Component57.LeafB4_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_2.selectedEquations, Krenn.Component57.LeafB4_2_2.selectedIndices, Krenn.Component57.LeafB4_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_2.selectedEquations, Krenn.Component57.LeafB4_2_2.selectedIndices, Krenn.Component57.LeafB4_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_2.selectedEquations, Krenn.Component57.LeafB4_2_2.selectedIndices, Krenn.Component57.LeafB4_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_2.selectedEquations, Krenn.Component57.LeafB4_2_2.selectedIndices, Krenn.Component57.LeafB4_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_2.selectedEquations, Krenn.Component57.LeafB4_2_2.selectedIndices, Krenn.Component57.LeafB4_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_2.selectedEquations, Krenn.Component57.LeafB4_2_2.selectedIndices, Krenn.Component57.LeafB4_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.2.3`. -/
theorem leafB423Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB4_2_3.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_3.selectedEquations, Krenn.Component57.LeafB4_2_3.selectedIndices, Krenn.Component57.LeafB4_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.2.4`. -/
theorem leafB424Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else d2Inverse0
  apply Krenn.Component57.LeafB4_2_4.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_4.selectedEquations, Krenn.Component57.LeafB4_2_4.selectedIndices, Krenn.Component57.LeafB4_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.2.5`. -/
theorem leafB425Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d2Inverse0
    else d2Inverse2
  apply Krenn.Component57.LeafB4_2_5.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨200, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨216, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨219, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨246, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨289, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨358, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨499, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨519, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨524, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨535, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨599, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨600, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨614, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨616, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨617, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨618, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨619, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨620, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨621, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨622, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨624, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨627, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨629, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨630, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨640, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨641, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨642, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨645, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨658, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨659, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨666, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨667, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨668, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨669, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_5.selectedEquations, Krenn.Component57.LeafB4_2_5.selectedIndices, Krenn.Component57.LeafB4_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.2.6`. -/
theorem leafB426Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d2Inverse0
    else d2Inverse1
  apply Krenn.Component57.LeafB4_2_6.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_6.selectedEquations, Krenn.Component57.LeafB4_2_6.selectedIndices, Krenn.Component57.LeafB4_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_6.selectedEquations, Krenn.Component57.LeafB4_2_6.selectedIndices, Krenn.Component57.LeafB4_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_6.selectedEquations, Krenn.Component57.LeafB4_2_6.selectedIndices, Krenn.Component57.LeafB4_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_6.selectedEquations, Krenn.Component57.LeafB4_2_6.selectedIndices, Krenn.Component57.LeafB4_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_6.selectedEquations, Krenn.Component57.LeafB4_2_6.selectedIndices, Krenn.Component57.LeafB4_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_6.selectedEquations, Krenn.Component57.LeafB4_2_6.selectedIndices, Krenn.Component57.LeafB4_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_6.selectedEquations, Krenn.Component57.LeafB4_2_6.selectedIndices, Krenn.Component57.LeafB4_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_6.selectedEquations, Krenn.Component57.LeafB4_2_6.selectedIndices, Krenn.Component57.LeafB4_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_6.selectedEquations, Krenn.Component57.LeafB4_2_6.selectedIndices, Krenn.Component57.LeafB4_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_6.selectedEquations, Krenn.Component57.LeafB4_2_6.selectedIndices, Krenn.Component57.LeafB4_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_6.selectedEquations, Krenn.Component57.LeafB4_2_6.selectedIndices, Krenn.Component57.LeafB4_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_6.selectedEquations, Krenn.Component57.LeafB4_2_6.selectedIndices, Krenn.Component57.LeafB4_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_6.selectedEquations, Krenn.Component57.LeafB4_2_6.selectedIndices, Krenn.Component57.LeafB4_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_6.selectedEquations, Krenn.Component57.LeafB4_2_6.selectedIndices, Krenn.Component57.LeafB4_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.2.7`. -/
theorem leafB427Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d2Inverse0
    else if at1 : index.val = 65 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB4_2_7.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_2_7.selectedEquations, Krenn.Component57.LeafB4_2_7.selectedIndices, Krenn.Component57.LeafB4_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.3.0`. -/
theorem leafB430Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 65 → R := values2
  apply Krenn.Component57.LeafB4_3_0.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_0.selectedEquations, Krenn.Component57.LeafB4_3_0.selectedIndices, Krenn.Component57.LeafB4_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.3.1`. -/
theorem leafB431Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component57.LeafB4_3_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_1.selectedEquations, Krenn.Component57.LeafB4_3_1.selectedIndices, Krenn.Component57.LeafB4_3_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_1.selectedEquations, Krenn.Component57.LeafB4_3_1.selectedIndices, Krenn.Component57.LeafB4_3_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_1.selectedEquations, Krenn.Component57.LeafB4_3_1.selectedIndices, Krenn.Component57.LeafB4_3_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_1.selectedEquations, Krenn.Component57.LeafB4_3_1.selectedIndices, Krenn.Component57.LeafB4_3_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_1.selectedEquations, Krenn.Component57.LeafB4_3_1.selectedIndices, Krenn.Component57.LeafB4_3_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_1.selectedEquations, Krenn.Component57.LeafB4_3_1.selectedIndices, Krenn.Component57.LeafB4_3_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_1.selectedEquations, Krenn.Component57.LeafB4_3_1.selectedIndices, Krenn.Component57.LeafB4_3_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.3.2`. -/
theorem leafB432Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  apply Krenn.Component57.LeafB4_3_2.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨296, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨390, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨437, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨474, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨524, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨618, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨619, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨620, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨621, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨669, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_2.selectedEquations, Krenn.Component57.LeafB4_3_2.selectedIndices, Krenn.Component57.LeafB4_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.3.3`. -/
theorem leafB433Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB4_3_3.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨358, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨390, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨524, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨618, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨619, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨620, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨621, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨669, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_3.selectedEquations, Krenn.Component57.LeafB4_3_3.selectedIndices, Krenn.Component57.LeafB4_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.3.4`. -/
theorem leafB434Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else d2Inverse0
  apply Krenn.Component57.LeafB4_3_4.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_4.selectedEquations, Krenn.Component57.LeafB4_3_4.selectedIndices, Krenn.Component57.LeafB4_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.3.5`. -/
theorem leafB435Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse0
    else d2Inverse2
  apply Krenn.Component57.LeafB4_3_5.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_5.selectedEquations, Krenn.Component57.LeafB4_3_5.selectedIndices, Krenn.Component57.LeafB4_3_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_5.selectedEquations, Krenn.Component57.LeafB4_3_5.selectedIndices, Krenn.Component57.LeafB4_3_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_5.selectedEquations, Krenn.Component57.LeafB4_3_5.selectedIndices, Krenn.Component57.LeafB4_3_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_5.selectedEquations, Krenn.Component57.LeafB4_3_5.selectedIndices, Krenn.Component57.LeafB4_3_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_5.selectedEquations, Krenn.Component57.LeafB4_3_5.selectedIndices, Krenn.Component57.LeafB4_3_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_5.selectedEquations, Krenn.Component57.LeafB4_3_5.selectedIndices, Krenn.Component57.LeafB4_3_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_5.selectedEquations, Krenn.Component57.LeafB4_3_5.selectedIndices, Krenn.Component57.LeafB4_3_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.3.6`. -/
theorem leafB436Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse0
    else d2Inverse1
  apply Krenn.Component57.LeafB4_3_6.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨296, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨390, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨437, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨474, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨524, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨618, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨619, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨620, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨621, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨669, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_6.selectedEquations, Krenn.Component57.LeafB4_3_6.selectedIndices, Krenn.Component57.LeafB4_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.3.7`. -/
theorem leafB437Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse0
    else if at1 : index.val = 66 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB4_3_7.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨358, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨390, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨524, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨618, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨619, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨620, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨621, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨669, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_3_7.selectedEquations, Krenn.Component57.LeafB4_3_7.selectedIndices, Krenn.Component57.LeafB4_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.4`. -/
theorem leafB44Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.Component57.LeafB4_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_4.selectedEquations, Krenn.Component57.LeafB4_4.selectedIndices, Krenn.Component57.LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_4.selectedEquations, Krenn.Component57.LeafB4_4.selectedIndices, Krenn.Component57.LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_4.selectedEquations, Krenn.Component57.LeafB4_4.selectedIndices, Krenn.Component57.LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_4.selectedEquations, Krenn.Component57.LeafB4_4.selectedIndices, Krenn.Component57.LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_4.selectedEquations, Krenn.Component57.LeafB4_4.selectedIndices, Krenn.Component57.LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_4.selectedEquations, Krenn.Component57.LeafB4_4.selectedIndices, Krenn.Component57.LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_4.selectedEquations, Krenn.Component57.LeafB4_4.selectedIndices, Krenn.Component57.LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_4.selectedEquations, Krenn.Component57.LeafB4_4.selectedIndices, Krenn.Component57.LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_4.selectedEquations, Krenn.Component57.LeafB4_4.selectedIndices, Krenn.Component57.LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_4.selectedEquations, Krenn.Component57.LeafB4_4.selectedIndices, Krenn.Component57.LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_4.selectedEquations, Krenn.Component57.LeafB4_4.selectedIndices, Krenn.Component57.LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_4.selectedEquations, Krenn.Component57.LeafB4_4.selectedIndices, Krenn.Component57.LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_4.selectedEquations, Krenn.Component57.LeafB4_4.selectedIndices, Krenn.Component57.LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_4.selectedEquations, Krenn.Component57.LeafB4_4.selectedIndices, Krenn.Component57.LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_4.selectedEquations, Krenn.Component57.LeafB4_4.selectedIndices, Krenn.Component57.LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_4.selectedEquations, Krenn.Component57.LeafB4_4.selectedIndices, Krenn.Component57.LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_4.selectedEquations, Krenn.Component57.LeafB4_4.selectedIndices, Krenn.Component57.LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.5`. -/
theorem leafB45Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.Component57.LeafB4_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨330, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨516, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_5.selectedEquations, Krenn.Component57.LeafB4_5.selectedIndices, Krenn.Component57.LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b4.6.0`. -/
theorem leafB460Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 65 → R := values2
  apply Krenn.Component57.LeafB4_6_0.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_0.selectedEquations, Krenn.Component57.LeafB4_6_0.selectedIndices, Krenn.Component57.LeafB4_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.6.1`. -/
theorem leafB461Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component57.LeafB4_6_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨219, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨461, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨485, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨525, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨535, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨620, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨621, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨669, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_1.selectedEquations, Krenn.Component57.LeafB4_6_1.selectedIndices, Krenn.Component57.LeafB4_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.6.2`. -/
theorem leafB462Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  apply Krenn.Component57.LeafB4_6_2.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_2.selectedEquations, Krenn.Component57.LeafB4_6_2.selectedIndices, Krenn.Component57.LeafB4_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_2.selectedEquations, Krenn.Component57.LeafB4_6_2.selectedIndices, Krenn.Component57.LeafB4_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_2.selectedEquations, Krenn.Component57.LeafB4_6_2.selectedIndices, Krenn.Component57.LeafB4_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_2.selectedEquations, Krenn.Component57.LeafB4_6_2.selectedIndices, Krenn.Component57.LeafB4_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_2.selectedEquations, Krenn.Component57.LeafB4_6_2.selectedIndices, Krenn.Component57.LeafB4_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_2.selectedEquations, Krenn.Component57.LeafB4_6_2.selectedIndices, Krenn.Component57.LeafB4_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_2.selectedEquations, Krenn.Component57.LeafB4_6_2.selectedIndices, Krenn.Component57.LeafB4_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_2.selectedEquations, Krenn.Component57.LeafB4_6_2.selectedIndices, Krenn.Component57.LeafB4_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_2.selectedEquations, Krenn.Component57.LeafB4_6_2.selectedIndices, Krenn.Component57.LeafB4_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_2.selectedEquations, Krenn.Component57.LeafB4_6_2.selectedIndices, Krenn.Component57.LeafB4_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_2.selectedEquations, Krenn.Component57.LeafB4_6_2.selectedIndices, Krenn.Component57.LeafB4_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_2.selectedEquations, Krenn.Component57.LeafB4_6_2.selectedIndices, Krenn.Component57.LeafB4_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_2.selectedEquations, Krenn.Component57.LeafB4_6_2.selectedIndices, Krenn.Component57.LeafB4_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_2.selectedEquations, Krenn.Component57.LeafB4_6_2.selectedIndices, Krenn.Component57.LeafB4_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.6.3`. -/
theorem leafB463Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB4_6_3.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_3.selectedEquations, Krenn.Component57.LeafB4_6_3.selectedIndices, Krenn.Component57.LeafB4_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.6.4`. -/
theorem leafB464Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else d2Inverse0
  apply Krenn.Component57.LeafB4_6_4.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_4.selectedEquations, Krenn.Component57.LeafB4_6_4.selectedIndices, Krenn.Component57.LeafB4_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.6.5`. -/
theorem leafB465Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse0
    else d2Inverse2
  apply Krenn.Component57.LeafB4_6_5.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨370, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨615, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_5.selectedEquations, Krenn.Component57.LeafB4_6_5.selectedIndices, Krenn.Component57.LeafB4_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.6.6`. -/
theorem leafB466Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse0
    else d2Inverse1
  apply Krenn.Component57.LeafB4_6_6.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_6.selectedEquations, Krenn.Component57.LeafB4_6_6.selectedIndices, Krenn.Component57.LeafB4_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_6.selectedEquations, Krenn.Component57.LeafB4_6_6.selectedIndices, Krenn.Component57.LeafB4_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_6.selectedEquations, Krenn.Component57.LeafB4_6_6.selectedIndices, Krenn.Component57.LeafB4_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_6.selectedEquations, Krenn.Component57.LeafB4_6_6.selectedIndices, Krenn.Component57.LeafB4_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_6.selectedEquations, Krenn.Component57.LeafB4_6_6.selectedIndices, Krenn.Component57.LeafB4_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_6.selectedEquations, Krenn.Component57.LeafB4_6_6.selectedIndices, Krenn.Component57.LeafB4_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_6.selectedEquations, Krenn.Component57.LeafB4_6_6.selectedIndices, Krenn.Component57.LeafB4_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_6.selectedEquations, Krenn.Component57.LeafB4_6_6.selectedIndices, Krenn.Component57.LeafB4_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_6.selectedEquations, Krenn.Component57.LeafB4_6_6.selectedIndices, Krenn.Component57.LeafB4_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_6.selectedEquations, Krenn.Component57.LeafB4_6_6.selectedIndices, Krenn.Component57.LeafB4_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_6.selectedEquations, Krenn.Component57.LeafB4_6_6.selectedIndices, Krenn.Component57.LeafB4_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_6.selectedEquations, Krenn.Component57.LeafB4_6_6.selectedIndices, Krenn.Component57.LeafB4_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_6.selectedEquations, Krenn.Component57.LeafB4_6_6.selectedIndices, Krenn.Component57.LeafB4_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_6.selectedEquations, Krenn.Component57.LeafB4_6_6.selectedIndices, Krenn.Component57.LeafB4_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.6.7`. -/
theorem leafB467Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse0
    else if at1 : index.val = 66 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB4_6_7.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_6_7.selectedEquations, Krenn.Component57.LeafB4_6_7.selectedIndices, Krenn.Component57.LeafB4_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.7.0`. -/
theorem leafB470Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else if at1 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 66 → R := values2
  apply Krenn.Component57.LeafB4_7_0.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_0.selectedEquations, Krenn.Component57.LeafB4_7_0.selectedIndices, Krenn.Component57.LeafB4_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.7.1`. -/
theorem leafB471Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else if at1 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component57.LeafB4_7_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_1.selectedEquations, Krenn.Component57.LeafB4_7_1.selectedIndices, Krenn.Component57.LeafB4_7_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_1.selectedEquations, Krenn.Component57.LeafB4_7_1.selectedIndices, Krenn.Component57.LeafB4_7_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_1.selectedEquations, Krenn.Component57.LeafB4_7_1.selectedIndices, Krenn.Component57.LeafB4_7_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_1.selectedEquations, Krenn.Component57.LeafB4_7_1.selectedIndices, Krenn.Component57.LeafB4_7_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_1.selectedEquations, Krenn.Component57.LeafB4_7_1.selectedIndices, Krenn.Component57.LeafB4_7_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_1.selectedEquations, Krenn.Component57.LeafB4_7_1.selectedIndices, Krenn.Component57.LeafB4_7_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_1.selectedEquations, Krenn.Component57.LeafB4_7_1.selectedIndices, Krenn.Component57.LeafB4_7_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.7.2`. -/
theorem leafB472Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else if at1 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  apply Krenn.Component57.LeafB4_7_2.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨77, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨84, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨296, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨390, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨437, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨474, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨618, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨619, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨620, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨621, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨669, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_2.selectedEquations, Krenn.Component57.LeafB4_7_2.selectedIndices, Krenn.Component57.LeafB4_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.7.3`. -/
theorem leafB473Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else if at1 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 66 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB4_7_3.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨516, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_3.selectedEquations, Krenn.Component57.LeafB4_7_3.selectedIndices, Krenn.Component57.LeafB4_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.7.4`. -/
theorem leafB474Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else if at1 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else d2Inverse0
  apply Krenn.Component57.LeafB4_7_4.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_4.selectedEquations, Krenn.Component57.LeafB4_7_4.selectedIndices, Krenn.Component57.LeafB4_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.7.5`. -/
theorem leafB475Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else if at1 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 66 then
      d2Inverse0
    else d2Inverse2
  apply Krenn.Component57.LeafB4_7_5.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_5.selectedEquations, Krenn.Component57.LeafB4_7_5.selectedIndices, Krenn.Component57.LeafB4_7_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_5.selectedEquations, Krenn.Component57.LeafB4_7_5.selectedIndices, Krenn.Component57.LeafB4_7_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_5.selectedEquations, Krenn.Component57.LeafB4_7_5.selectedIndices, Krenn.Component57.LeafB4_7_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_5.selectedEquations, Krenn.Component57.LeafB4_7_5.selectedIndices, Krenn.Component57.LeafB4_7_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_5.selectedEquations, Krenn.Component57.LeafB4_7_5.selectedIndices, Krenn.Component57.LeafB4_7_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_5.selectedEquations, Krenn.Component57.LeafB4_7_5.selectedIndices, Krenn.Component57.LeafB4_7_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_5.selectedEquations, Krenn.Component57.LeafB4_7_5.selectedIndices, Krenn.Component57.LeafB4_7_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.7.6`. -/
theorem leafB476Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else if at1 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 66 then
      d2Inverse0
    else d2Inverse1
  apply Krenn.Component57.LeafB4_7_6.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨77, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨84, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨296, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨390, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨437, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨474, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨618, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨619, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨620, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨621, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨669, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_6.selectedEquations, Krenn.Component57.LeafB4_7_6.selectedIndices, Krenn.Component57.LeafB4_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b4.7.7`. -/
theorem leafB477Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else if at1 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 69 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 66 then
      d2Inverse0
    else if at1 : index.val = 67 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB4_7_7.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨516, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB4_7_7.selectedEquations, Krenn.Component57.LeafB4_7_7.selectedIndices, Krenn.Component57.LeafB4_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b5`. -/
theorem leafB5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse2
  apply Krenn.Component57.LeafB5.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨165, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨330, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨481, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨487, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨520, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨623, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB5.selectedEquations, Krenn.Component57.LeafB5.selectedIndices, Krenn.Component57.LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.0`. -/
theorem leafB60Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 64 → R := values1
  apply Krenn.Component57.LeafB6_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_0.selectedEquations, Krenn.Component57.LeafB6_0.selectedIndices, Krenn.Component57.LeafB6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_0.selectedEquations, Krenn.Component57.LeafB6_0.selectedIndices, Krenn.Component57.LeafB6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_0.selectedEquations, Krenn.Component57.LeafB6_0.selectedIndices, Krenn.Component57.LeafB6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_0.selectedEquations, Krenn.Component57.LeafB6_0.selectedIndices, Krenn.Component57.LeafB6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_0.selectedEquations, Krenn.Component57.LeafB6_0.selectedIndices, Krenn.Component57.LeafB6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_0.selectedEquations, Krenn.Component57.LeafB6_0.selectedIndices, Krenn.Component57.LeafB6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_0.selectedEquations, Krenn.Component57.LeafB6_0.selectedIndices, Krenn.Component57.LeafB6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_0.selectedEquations, Krenn.Component57.LeafB6_0.selectedIndices, Krenn.Component57.LeafB6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_0.selectedEquations, Krenn.Component57.LeafB6_0.selectedIndices, Krenn.Component57.LeafB6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_0.selectedEquations, Krenn.Component57.LeafB6_0.selectedIndices, Krenn.Component57.LeafB6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_0.selectedEquations, Krenn.Component57.LeafB6_0.selectedIndices, Krenn.Component57.LeafB6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_0.selectedEquations, Krenn.Component57.LeafB6_0.selectedIndices, Krenn.Component57.LeafB6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_0.selectedEquations, Krenn.Component57.LeafB6_0.selectedIndices, Krenn.Component57.LeafB6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_0.selectedEquations, Krenn.Component57.LeafB6_0.selectedIndices, Krenn.Component57.LeafB6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_0.selectedEquations, Krenn.Component57.LeafB6_0.selectedIndices, Krenn.Component57.LeafB6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_0.selectedEquations, Krenn.Component57.LeafB6_0.selectedIndices, Krenn.Component57.LeafB6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_0.selectedEquations, Krenn.Component57.LeafB6_0.selectedIndices, Krenn.Component57.LeafB6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.1.0`. -/
theorem leafB610Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 65 → R := values2
  apply Krenn.Component57.LeafB6_1_0.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_0.selectedEquations, Krenn.Component57.LeafB6_1_0.selectedIndices, Krenn.Component57.LeafB6_1_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.1.1`. -/
theorem leafB611Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component57.LeafB6_1_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_1.selectedEquations, Krenn.Component57.LeafB6_1_1.selectedIndices, Krenn.Component57.LeafB6_1_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.1.2`. -/
theorem leafB612Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  apply Krenn.Component57.LeafB6_1_2.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨485, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨491, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨622, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_2.selectedEquations, Krenn.Component57.LeafB6_1_2.selectedIndices, Krenn.Component57.LeafB6_1_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.1.3`. -/
theorem leafB613Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB6_1_3.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_3.selectedEquations, Krenn.Component57.LeafB6_1_3.selectedIndices, Krenn.Component57.LeafB6_1_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_3.selectedEquations, Krenn.Component57.LeafB6_1_3.selectedIndices, Krenn.Component57.LeafB6_1_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_3.selectedEquations, Krenn.Component57.LeafB6_1_3.selectedIndices, Krenn.Component57.LeafB6_1_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.1.4`. -/
theorem leafB614Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else d2Inverse0
  apply Krenn.Component57.LeafB6_1_4.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_4.selectedEquations, Krenn.Component57.LeafB6_1_4.selectedIndices, Krenn.Component57.LeafB6_1_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.1.5`. -/
theorem leafB615Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse0
    else d2Inverse2
  apply Krenn.Component57.LeafB6_1_5.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_5.selectedEquations, Krenn.Component57.LeafB6_1_5.selectedIndices, Krenn.Component57.LeafB6_1_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.1.6`. -/
theorem leafB616Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse0
    else d2Inverse1
  apply Krenn.Component57.LeafB6_1_6.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨485, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨491, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨622, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_6.selectedEquations, Krenn.Component57.LeafB6_1_6.selectedIndices, Krenn.Component57.LeafB6_1_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.1.7`. -/
theorem leafB617Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse0
    else if at1 : index.val = 66 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB6_1_7.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_7.selectedEquations, Krenn.Component57.LeafB6_1_7.selectedIndices, Krenn.Component57.LeafB6_1_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_7.selectedEquations, Krenn.Component57.LeafB6_1_7.selectedIndices, Krenn.Component57.LeafB6_1_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_1_7.selectedEquations, Krenn.Component57.LeafB6_1_7.selectedIndices, Krenn.Component57.LeafB6_1_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.2.0`. -/
theorem leafB620Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 65 → R := values2
  apply Krenn.Component57.LeafB6_2_0.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_0.selectedEquations, Krenn.Component57.LeafB6_2_0.selectedIndices, Krenn.Component57.LeafB6_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_0.selectedEquations, Krenn.Component57.LeafB6_2_0.selectedIndices, Krenn.Component57.LeafB6_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_0.selectedEquations, Krenn.Component57.LeafB6_2_0.selectedIndices, Krenn.Component57.LeafB6_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_0.selectedEquations, Krenn.Component57.LeafB6_2_0.selectedIndices, Krenn.Component57.LeafB6_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_0.selectedEquations, Krenn.Component57.LeafB6_2_0.selectedIndices, Krenn.Component57.LeafB6_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_0.selectedEquations, Krenn.Component57.LeafB6_2_0.selectedIndices, Krenn.Component57.LeafB6_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨334, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_0.selectedEquations, Krenn.Component57.LeafB6_2_0.selectedIndices, Krenn.Component57.LeafB6_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_0.selectedEquations, Krenn.Component57.LeafB6_2_0.selectedIndices, Krenn.Component57.LeafB6_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_0.selectedEquations, Krenn.Component57.LeafB6_2_0.selectedIndices, Krenn.Component57.LeafB6_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_0.selectedEquations, Krenn.Component57.LeafB6_2_0.selectedIndices, Krenn.Component57.LeafB6_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_0.selectedEquations, Krenn.Component57.LeafB6_2_0.selectedIndices, Krenn.Component57.LeafB6_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_0.selectedEquations, Krenn.Component57.LeafB6_2_0.selectedIndices, Krenn.Component57.LeafB6_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_0.selectedEquations, Krenn.Component57.LeafB6_2_0.selectedIndices, Krenn.Component57.LeafB6_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_0.selectedEquations, Krenn.Component57.LeafB6_2_0.selectedIndices, Krenn.Component57.LeafB6_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_0.selectedEquations, Krenn.Component57.LeafB6_2_0.selectedIndices, Krenn.Component57.LeafB6_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_0.selectedEquations, Krenn.Component57.LeafB6_2_0.selectedIndices, Krenn.Component57.LeafB6_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_0.selectedEquations, Krenn.Component57.LeafB6_2_0.selectedIndices, Krenn.Component57.LeafB6_2_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.2.1`. -/
theorem leafB621Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component57.LeafB6_2_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨219, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨535, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨616, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨617, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨627, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨659, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨668, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_1.selectedEquations, Krenn.Component57.LeafB6_2_1.selectedIndices, Krenn.Component57.LeafB6_2_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.2.2`. -/
theorem leafB622Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  apply Krenn.Component57.LeafB6_2_2.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_2.selectedEquations, Krenn.Component57.LeafB6_2_2.selectedIndices, Krenn.Component57.LeafB6_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_2.selectedEquations, Krenn.Component57.LeafB6_2_2.selectedIndices, Krenn.Component57.LeafB6_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_2.selectedEquations, Krenn.Component57.LeafB6_2_2.selectedIndices, Krenn.Component57.LeafB6_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_2.selectedEquations, Krenn.Component57.LeafB6_2_2.selectedIndices, Krenn.Component57.LeafB6_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_2.selectedEquations, Krenn.Component57.LeafB6_2_2.selectedIndices, Krenn.Component57.LeafB6_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_2.selectedEquations, Krenn.Component57.LeafB6_2_2.selectedIndices, Krenn.Component57.LeafB6_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_2.selectedEquations, Krenn.Component57.LeafB6_2_2.selectedIndices, Krenn.Component57.LeafB6_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_2.selectedEquations, Krenn.Component57.LeafB6_2_2.selectedIndices, Krenn.Component57.LeafB6_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_2.selectedEquations, Krenn.Component57.LeafB6_2_2.selectedIndices, Krenn.Component57.LeafB6_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_2.selectedEquations, Krenn.Component57.LeafB6_2_2.selectedIndices, Krenn.Component57.LeafB6_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_2.selectedEquations, Krenn.Component57.LeafB6_2_2.selectedIndices, Krenn.Component57.LeafB6_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_2.selectedEquations, Krenn.Component57.LeafB6_2_2.selectedIndices, Krenn.Component57.LeafB6_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_2.selectedEquations, Krenn.Component57.LeafB6_2_2.selectedIndices, Krenn.Component57.LeafB6_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_2.selectedEquations, Krenn.Component57.LeafB6_2_2.selectedIndices, Krenn.Component57.LeafB6_2_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.2.3`. -/
theorem leafB623Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB6_2_3.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_3.selectedEquations, Krenn.Component57.LeafB6_2_3.selectedIndices, Krenn.Component57.LeafB6_2_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.2.4`. -/
theorem leafB624Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else d2Inverse0
  apply Krenn.Component57.LeafB6_2_4.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_4.selectedEquations, Krenn.Component57.LeafB6_2_4.selectedIndices, Krenn.Component57.LeafB6_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_4.selectedEquations, Krenn.Component57.LeafB6_2_4.selectedIndices, Krenn.Component57.LeafB6_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_4.selectedEquations, Krenn.Component57.LeafB6_2_4.selectedIndices, Krenn.Component57.LeafB6_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_4.selectedEquations, Krenn.Component57.LeafB6_2_4.selectedIndices, Krenn.Component57.LeafB6_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_4.selectedEquations, Krenn.Component57.LeafB6_2_4.selectedIndices, Krenn.Component57.LeafB6_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_4.selectedEquations, Krenn.Component57.LeafB6_2_4.selectedIndices, Krenn.Component57.LeafB6_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨334, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_4.selectedEquations, Krenn.Component57.LeafB6_2_4.selectedIndices, Krenn.Component57.LeafB6_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_4.selectedEquations, Krenn.Component57.LeafB6_2_4.selectedIndices, Krenn.Component57.LeafB6_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_4.selectedEquations, Krenn.Component57.LeafB6_2_4.selectedIndices, Krenn.Component57.LeafB6_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_4.selectedEquations, Krenn.Component57.LeafB6_2_4.selectedIndices, Krenn.Component57.LeafB6_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_4.selectedEquations, Krenn.Component57.LeafB6_2_4.selectedIndices, Krenn.Component57.LeafB6_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_4.selectedEquations, Krenn.Component57.LeafB6_2_4.selectedIndices, Krenn.Component57.LeafB6_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_4.selectedEquations, Krenn.Component57.LeafB6_2_4.selectedIndices, Krenn.Component57.LeafB6_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_4.selectedEquations, Krenn.Component57.LeafB6_2_4.selectedIndices, Krenn.Component57.LeafB6_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_4.selectedEquations, Krenn.Component57.LeafB6_2_4.selectedIndices, Krenn.Component57.LeafB6_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_4.selectedEquations, Krenn.Component57.LeafB6_2_4.selectedIndices, Krenn.Component57.LeafB6_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_4.selectedEquations, Krenn.Component57.LeafB6_2_4.selectedIndices, Krenn.Component57.LeafB6_2_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.2.5`. -/
theorem leafB625Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse0
    else d2Inverse2
  apply Krenn.Component57.LeafB6_2_5.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨200, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨216, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨219, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨246, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨289, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨358, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨465, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨519, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨524, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨535, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨598, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨599, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨600, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨614, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨616, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨617, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨618, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨619, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨620, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨621, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨622, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨624, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨627, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨629, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨640, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨641, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨643, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨644, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨650, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨658, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨659, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨666, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨667, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨668, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨669, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_5.selectedEquations, Krenn.Component57.LeafB6_2_5.selectedIndices, Krenn.Component57.LeafB6_2_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.2.6`. -/
theorem leafB626Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse0
    else d2Inverse1
  apply Krenn.Component57.LeafB6_2_6.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_6.selectedEquations, Krenn.Component57.LeafB6_2_6.selectedIndices, Krenn.Component57.LeafB6_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_6.selectedEquations, Krenn.Component57.LeafB6_2_6.selectedIndices, Krenn.Component57.LeafB6_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_6.selectedEquations, Krenn.Component57.LeafB6_2_6.selectedIndices, Krenn.Component57.LeafB6_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_6.selectedEquations, Krenn.Component57.LeafB6_2_6.selectedIndices, Krenn.Component57.LeafB6_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_6.selectedEquations, Krenn.Component57.LeafB6_2_6.selectedIndices, Krenn.Component57.LeafB6_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_6.selectedEquations, Krenn.Component57.LeafB6_2_6.selectedIndices, Krenn.Component57.LeafB6_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_6.selectedEquations, Krenn.Component57.LeafB6_2_6.selectedIndices, Krenn.Component57.LeafB6_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_6.selectedEquations, Krenn.Component57.LeafB6_2_6.selectedIndices, Krenn.Component57.LeafB6_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_6.selectedEquations, Krenn.Component57.LeafB6_2_6.selectedIndices, Krenn.Component57.LeafB6_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_6.selectedEquations, Krenn.Component57.LeafB6_2_6.selectedIndices, Krenn.Component57.LeafB6_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_6.selectedEquations, Krenn.Component57.LeafB6_2_6.selectedIndices, Krenn.Component57.LeafB6_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_6.selectedEquations, Krenn.Component57.LeafB6_2_6.selectedIndices, Krenn.Component57.LeafB6_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_6.selectedEquations, Krenn.Component57.LeafB6_2_6.selectedIndices, Krenn.Component57.LeafB6_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_6.selectedEquations, Krenn.Component57.LeafB6_2_6.selectedIndices, Krenn.Component57.LeafB6_2_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.2.7`. -/
theorem leafB627Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse0
    else if at1 : index.val = 66 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB6_2_7.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_2_7.selectedEquations, Krenn.Component57.LeafB6_2_7.selectedIndices, Krenn.Component57.LeafB6_2_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.3.0`. -/
theorem leafB630Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 66 → R := values2
  apply Krenn.Component57.LeafB6_3_0.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨334, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨339, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨460, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_0.selectedEquations, Krenn.Component57.LeafB6_3_0.selectedIndices, Krenn.Component57.LeafB6_3_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.3.1`. -/
theorem leafB631Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component57.LeafB6_3_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_1.selectedEquations, Krenn.Component57.LeafB6_3_1.selectedIndices, Krenn.Component57.LeafB6_3_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_1.selectedEquations, Krenn.Component57.LeafB6_3_1.selectedIndices, Krenn.Component57.LeafB6_3_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_1.selectedEquations, Krenn.Component57.LeafB6_3_1.selectedIndices, Krenn.Component57.LeafB6_3_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_1.selectedEquations, Krenn.Component57.LeafB6_3_1.selectedIndices, Krenn.Component57.LeafB6_3_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_1.selectedEquations, Krenn.Component57.LeafB6_3_1.selectedIndices, Krenn.Component57.LeafB6_3_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_1.selectedEquations, Krenn.Component57.LeafB6_3_1.selectedIndices, Krenn.Component57.LeafB6_3_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_1.selectedEquations, Krenn.Component57.LeafB6_3_1.selectedIndices, Krenn.Component57.LeafB6_3_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.3.2`. -/
theorem leafB632Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  apply Krenn.Component57.LeafB6_3_2.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨185, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨309, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_2.selectedEquations, Krenn.Component57.LeafB6_3_2.selectedIndices, Krenn.Component57.LeafB6_3_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.3.3`. -/
theorem leafB633Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 66 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB6_3_3.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨72, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨228, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨616, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨617, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨668, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_3.selectedEquations, Krenn.Component57.LeafB6_3_3.selectedIndices, Krenn.Component57.LeafB6_3_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.3.4`. -/
theorem leafB634Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else d2Inverse0
  apply Krenn.Component57.LeafB6_3_4.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨334, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨339, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨460, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_4.selectedEquations, Krenn.Component57.LeafB6_3_4.selectedIndices, Krenn.Component57.LeafB6_3_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.3.5`. -/
theorem leafB635Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 66 then
      d2Inverse0
    else d2Inverse2
  apply Krenn.Component57.LeafB6_3_5.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_5.selectedEquations, Krenn.Component57.LeafB6_3_5.selectedIndices, Krenn.Component57.LeafB6_3_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_5.selectedEquations, Krenn.Component57.LeafB6_3_5.selectedIndices, Krenn.Component57.LeafB6_3_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_5.selectedEquations, Krenn.Component57.LeafB6_3_5.selectedIndices, Krenn.Component57.LeafB6_3_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_5.selectedEquations, Krenn.Component57.LeafB6_3_5.selectedIndices, Krenn.Component57.LeafB6_3_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_5.selectedEquations, Krenn.Component57.LeafB6_3_5.selectedIndices, Krenn.Component57.LeafB6_3_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_5.selectedEquations, Krenn.Component57.LeafB6_3_5.selectedIndices, Krenn.Component57.LeafB6_3_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_5.selectedEquations, Krenn.Component57.LeafB6_3_5.selectedIndices, Krenn.Component57.LeafB6_3_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.3.6`. -/
theorem leafB636Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 66 then
      d2Inverse0
    else d2Inverse1
  apply Krenn.Component57.LeafB6_3_6.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨185, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨309, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_6.selectedEquations, Krenn.Component57.LeafB6_3_6.selectedIndices, Krenn.Component57.LeafB6_3_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.3.7`. -/
theorem leafB637Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 69 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 66 then
      d2Inverse0
    else if at1 : index.val = 67 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB6_3_7.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨72, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨228, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨616, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨617, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨668, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_3_7.selectedEquations, Krenn.Component57.LeafB6_3_7.selectedIndices, Krenn.Component57.LeafB6_3_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.4`. -/
theorem leafB64Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.Component57.LeafB6_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_4.selectedEquations, Krenn.Component57.LeafB6_4.selectedIndices, Krenn.Component57.LeafB6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_4.selectedEquations, Krenn.Component57.LeafB6_4.selectedIndices, Krenn.Component57.LeafB6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_4.selectedEquations, Krenn.Component57.LeafB6_4.selectedIndices, Krenn.Component57.LeafB6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_4.selectedEquations, Krenn.Component57.LeafB6_4.selectedIndices, Krenn.Component57.LeafB6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_4.selectedEquations, Krenn.Component57.LeafB6_4.selectedIndices, Krenn.Component57.LeafB6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_4.selectedEquations, Krenn.Component57.LeafB6_4.selectedIndices, Krenn.Component57.LeafB6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_4.selectedEquations, Krenn.Component57.LeafB6_4.selectedIndices, Krenn.Component57.LeafB6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_4.selectedEquations, Krenn.Component57.LeafB6_4.selectedIndices, Krenn.Component57.LeafB6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_4.selectedEquations, Krenn.Component57.LeafB6_4.selectedIndices, Krenn.Component57.LeafB6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_4.selectedEquations, Krenn.Component57.LeafB6_4.selectedIndices, Krenn.Component57.LeafB6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_4.selectedEquations, Krenn.Component57.LeafB6_4.selectedIndices, Krenn.Component57.LeafB6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_4.selectedEquations, Krenn.Component57.LeafB6_4.selectedIndices, Krenn.Component57.LeafB6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_4.selectedEquations, Krenn.Component57.LeafB6_4.selectedIndices, Krenn.Component57.LeafB6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_4.selectedEquations, Krenn.Component57.LeafB6_4.selectedIndices, Krenn.Component57.LeafB6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_4.selectedEquations, Krenn.Component57.LeafB6_4.selectedIndices, Krenn.Component57.LeafB6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_4.selectedEquations, Krenn.Component57.LeafB6_4.selectedIndices, Krenn.Component57.LeafB6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_4.selectedEquations, Krenn.Component57.LeafB6_4.selectedIndices, Krenn.Component57.LeafB6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.5`. -/
theorem leafB65Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.Component57.LeafB6_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨330, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨516, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_5.selectedEquations, Krenn.Component57.LeafB6_5.selectedIndices, Krenn.Component57.LeafB6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b6.6.0`. -/
theorem leafB660Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 66 → R := values2
  apply Krenn.Component57.LeafB6_6_0.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_0.selectedEquations, Krenn.Component57.LeafB6_6_0.selectedIndices, Krenn.Component57.LeafB6_6_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.6.1`. -/
theorem leafB661Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component57.LeafB6_6_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨165, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨200, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨216, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨219, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨461, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨485, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨520, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨525, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨535, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨620, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨621, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨669, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_1.selectedEquations, Krenn.Component57.LeafB6_6_1.selectedIndices, Krenn.Component57.LeafB6_6_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.6.2`. -/
theorem leafB662Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  apply Krenn.Component57.LeafB6_6_2.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_2.selectedEquations, Krenn.Component57.LeafB6_6_2.selectedIndices, Krenn.Component57.LeafB6_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_2.selectedEquations, Krenn.Component57.LeafB6_6_2.selectedIndices, Krenn.Component57.LeafB6_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_2.selectedEquations, Krenn.Component57.LeafB6_6_2.selectedIndices, Krenn.Component57.LeafB6_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_2.selectedEquations, Krenn.Component57.LeafB6_6_2.selectedIndices, Krenn.Component57.LeafB6_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_2.selectedEquations, Krenn.Component57.LeafB6_6_2.selectedIndices, Krenn.Component57.LeafB6_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_2.selectedEquations, Krenn.Component57.LeafB6_6_2.selectedIndices, Krenn.Component57.LeafB6_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_2.selectedEquations, Krenn.Component57.LeafB6_6_2.selectedIndices, Krenn.Component57.LeafB6_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_2.selectedEquations, Krenn.Component57.LeafB6_6_2.selectedIndices, Krenn.Component57.LeafB6_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_2.selectedEquations, Krenn.Component57.LeafB6_6_2.selectedIndices, Krenn.Component57.LeafB6_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_2.selectedEquations, Krenn.Component57.LeafB6_6_2.selectedIndices, Krenn.Component57.LeafB6_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_2.selectedEquations, Krenn.Component57.LeafB6_6_2.selectedIndices, Krenn.Component57.LeafB6_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_2.selectedEquations, Krenn.Component57.LeafB6_6_2.selectedIndices, Krenn.Component57.LeafB6_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_2.selectedEquations, Krenn.Component57.LeafB6_6_2.selectedIndices, Krenn.Component57.LeafB6_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_2.selectedEquations, Krenn.Component57.LeafB6_6_2.selectedIndices, Krenn.Component57.LeafB6_6_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.6.3`. -/
theorem leafB663Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 66 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB6_6_3.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_3.selectedEquations, Krenn.Component57.LeafB6_6_3.selectedIndices, Krenn.Component57.LeafB6_6_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.6.4`. -/
theorem leafB664Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else d2Inverse0
  apply Krenn.Component57.LeafB6_6_4.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_4.selectedEquations, Krenn.Component57.LeafB6_6_4.selectedIndices, Krenn.Component57.LeafB6_6_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.6.5`. -/
theorem leafB665Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 66 then
      d2Inverse0
    else d2Inverse2
  apply Krenn.Component57.LeafB6_6_5.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨370, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨615, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_5.selectedEquations, Krenn.Component57.LeafB6_6_5.selectedIndices, Krenn.Component57.LeafB6_6_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.6.6`. -/
theorem leafB666Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 66 then
      d2Inverse0
    else d2Inverse1
  apply Krenn.Component57.LeafB6_6_6.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_6.selectedEquations, Krenn.Component57.LeafB6_6_6.selectedIndices, Krenn.Component57.LeafB6_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_6.selectedEquations, Krenn.Component57.LeafB6_6_6.selectedIndices, Krenn.Component57.LeafB6_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_6.selectedEquations, Krenn.Component57.LeafB6_6_6.selectedIndices, Krenn.Component57.LeafB6_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_6.selectedEquations, Krenn.Component57.LeafB6_6_6.selectedIndices, Krenn.Component57.LeafB6_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_6.selectedEquations, Krenn.Component57.LeafB6_6_6.selectedIndices, Krenn.Component57.LeafB6_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_6.selectedEquations, Krenn.Component57.LeafB6_6_6.selectedIndices, Krenn.Component57.LeafB6_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_6.selectedEquations, Krenn.Component57.LeafB6_6_6.selectedIndices, Krenn.Component57.LeafB6_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_6.selectedEquations, Krenn.Component57.LeafB6_6_6.selectedIndices, Krenn.Component57.LeafB6_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_6.selectedEquations, Krenn.Component57.LeafB6_6_6.selectedIndices, Krenn.Component57.LeafB6_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_6.selectedEquations, Krenn.Component57.LeafB6_6_6.selectedIndices, Krenn.Component57.LeafB6_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_6.selectedEquations, Krenn.Component57.LeafB6_6_6.selectedIndices, Krenn.Component57.LeafB6_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_6.selectedEquations, Krenn.Component57.LeafB6_6_6.selectedIndices, Krenn.Component57.LeafB6_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_6.selectedEquations, Krenn.Component57.LeafB6_6_6.selectedIndices, Krenn.Component57.LeafB6_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_6.selectedEquations, Krenn.Component57.LeafB6_6_6.selectedIndices, Krenn.Component57.LeafB6_6_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.6.7`. -/
theorem leafB667Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 69 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 66 then
      d2Inverse0
    else if at1 : index.val = 67 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB6_6_7.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_6_7.selectedEquations, Krenn.Component57.LeafB6_6_7.selectedIndices, Krenn.Component57.LeafB6_6_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.7.0`. -/
theorem leafB670Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 67 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else if at1 : index.val = 65 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 67 → R := values2
  apply Krenn.Component57.LeafB6_7_0.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨77, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_0.selectedEquations, Krenn.Component57.LeafB6_7_0.selectedIndices, Krenn.Component57.LeafB6_7_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.7.1`. -/
theorem leafB671Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 67 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else if at1 : index.val = 65 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 67 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component57.LeafB6_7_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_1.selectedEquations, Krenn.Component57.LeafB6_7_1.selectedIndices, Krenn.Component57.LeafB6_7_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_1.selectedEquations, Krenn.Component57.LeafB6_7_1.selectedIndices, Krenn.Component57.LeafB6_7_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_1.selectedEquations, Krenn.Component57.LeafB6_7_1.selectedIndices, Krenn.Component57.LeafB6_7_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_1.selectedEquations, Krenn.Component57.LeafB6_7_1.selectedIndices, Krenn.Component57.LeafB6_7_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_1.selectedEquations, Krenn.Component57.LeafB6_7_1.selectedIndices, Krenn.Component57.LeafB6_7_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_1.selectedEquations, Krenn.Component57.LeafB6_7_1.selectedIndices, Krenn.Component57.LeafB6_7_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_1.selectedEquations, Krenn.Component57.LeafB6_7_1.selectedIndices, Krenn.Component57.LeafB6_7_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.7.2`. -/
theorem leafB672Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 67 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else if at1 : index.val = 65 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 67 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  apply Krenn.Component57.LeafB6_7_2.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨77, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_2.selectedEquations, Krenn.Component57.LeafB6_7_2.selectedIndices, Krenn.Component57.LeafB6_7_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.7.3`. -/
theorem leafB673Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 67 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else if at1 : index.val = 65 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 69 → R := fun index =>
    if inside : index.val < 67 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 67 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB6_7_3.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨516, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_3.selectedEquations, Krenn.Component57.LeafB6_7_3.selectedIndices, Krenn.Component57.LeafB6_7_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.7.4`. -/
theorem leafB674Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 67 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else if at1 : index.val = 65 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 67 then
      values2 ⟨index.val, inside⟩
    else d2Inverse0
  apply Krenn.Component57.LeafB6_7_4.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨77, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_4.selectedEquations, Krenn.Component57.LeafB6_7_4.selectedIndices, Krenn.Component57.LeafB6_7_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.7.5`. -/
theorem leafB675Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 67 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else if at1 : index.val = 65 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 69 → R := fun index =>
    if inside : index.val < 67 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 67 then
      d2Inverse0
    else d2Inverse2
  apply Krenn.Component57.LeafB6_7_5.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_5.selectedEquations, Krenn.Component57.LeafB6_7_5.selectedIndices, Krenn.Component57.LeafB6_7_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_5.selectedEquations, Krenn.Component57.LeafB6_7_5.selectedIndices, Krenn.Component57.LeafB6_7_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_5.selectedEquations, Krenn.Component57.LeafB6_7_5.selectedIndices, Krenn.Component57.LeafB6_7_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_5.selectedEquations, Krenn.Component57.LeafB6_7_5.selectedIndices, Krenn.Component57.LeafB6_7_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_5.selectedEquations, Krenn.Component57.LeafB6_7_5.selectedIndices, Krenn.Component57.LeafB6_7_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_5.selectedEquations, Krenn.Component57.LeafB6_7_5.selectedIndices, Krenn.Component57.LeafB6_7_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_5.selectedEquations, Krenn.Component57.LeafB6_7_5.selectedIndices, Krenn.Component57.LeafB6_7_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.7.6`. -/
theorem leafB676Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 67 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else if at1 : index.val = 65 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 69 → R := fun index =>
    if inside : index.val < 67 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 67 then
      d2Inverse0
    else d2Inverse1
  apply Krenn.Component57.LeafB6_7_6.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨77, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_6.selectedEquations, Krenn.Component57.LeafB6_7_6.selectedIndices, Krenn.Component57.LeafB6_7_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b6.7.7`. -/
theorem leafB677Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 67 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else if at1 : index.val = 65 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 70 → R := fun index =>
    if inside : index.val < 67 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 67 then
      d2Inverse0
    else if at1 : index.val = 68 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component57.LeafB6_7_7.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨516, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB6_7_7.selectedEquations, Krenn.Component57.LeafB6_7_7.selectedIndices, Krenn.Component57.LeafB6_7_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

/-- Frozen compatibility and contradiction for terminal chart `b7`. -/
theorem leafB7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 65 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else if at1 : index.val = 63 then
      d0Inverse1
    else d0Inverse2
  apply Krenn.Component57.LeafB7.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨165, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨330, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨481, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨487, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨520, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨623, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨670, by decide⟩
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.Component57.LeafB7.selectedEquations, Krenn.Component57.LeafB7.selectedIndices, Krenn.Component57.LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

/-- Recursive exhaustion of chart `b4.1`. -/
theorem nodeB41Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD2C0 : values 56 = 0
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB410Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact leafB411Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB412Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB413Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB414Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact leafB415Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB416Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB417Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])

/-- Recursive exhaustion of chart `b4.2`. -/
theorem nodeB42Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  by_cases zeroD2C0 : values 56 = 0
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB420Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact leafB421Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB422Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB423Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB424Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact leafB425Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB426Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB427Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])

/-- Recursive exhaustion of chart `b4.3`. -/
theorem nodeB43Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD2C0 : values 56 = 0
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB430Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact leafB431Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB432Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB433Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB434Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact leafB435Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB436Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB437Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])

/-- Recursive exhaustion of chart `b4.6`. -/
theorem nodeB46Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  by_cases zeroD2C0 : values 56 = 0
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB460Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact leafB461Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB462Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB463Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB464Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact leafB465Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB466Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB467Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])

/-- Recursive exhaustion of chart `b4.7`. -/
theorem nodeB47Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD2C0 : values 56 = 0
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB470Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact leafB471Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB472Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB473Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB474Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact leafB475Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB476Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB477Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])

/-- Recursive exhaustion of chart `b6.1`. -/
theorem nodeB61Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD2C0 : values 56 = 0
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB610Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact leafB611Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB612Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB613Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB614Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact leafB615Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB616Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB617Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])

/-- Recursive exhaustion of chart `b6.2`. -/
theorem nodeB62Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  by_cases zeroD2C0 : values 56 = 0
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB620Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact leafB621Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB622Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB623Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB624Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact leafB625Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB626Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB627Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])

/-- Recursive exhaustion of chart `b6.3`. -/
theorem nodeB63Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD2C0 : values 56 = 0
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB630Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact leafB631Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB632Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB633Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB634Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact leafB635Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB636Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB637Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])

/-- Recursive exhaustion of chart `b6.6`. -/
theorem nodeB66Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  by_cases zeroD2C0 : values 56 = 0
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB660Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact leafB661Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB662Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB663Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB664Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact leafB665Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB666Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB667Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])

/-- Recursive exhaustion of chart `b6.7`. -/
theorem nodeB67Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD2C0 : values 56 = 0
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB670Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact leafB671Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB672Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB673Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 57 = 0
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB674Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact leafB675Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 58)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 58 = 0
      · exact leafB676Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact leafB677Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 56)⁻¹ (by simp [zeroD2C0]) (values 57)⁻¹ (by simp [zeroD2C1]) (values 58)⁻¹ (by simp [zeroD2C2])

/-- Recursive exhaustion of chart `b0`. -/
theorem nodeB0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  by_cases zeroD1C0 : values 40 = 0
  ·
    by_cases zeroD1C1 : values 41 = 0
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact leafB00Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact leafB01Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 42)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact leafB02Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 41)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact leafB03Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 41)⁻¹ (by simp [zeroD1C1]) (values 42)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 41 = 0
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact leafB04Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact leafB05Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 42)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact leafB06Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) (values 41)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact leafB07Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) (values 41)⁻¹ (by simp [zeroD1C1]) (values 42)⁻¹ (by simp [zeroD1C2])

/-- Recursive exhaustion of chart `b2`. -/
theorem nodeB2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  by_cases zeroD1C0 : values 40 = 0
  ·
    by_cases zeroD1C1 : values 41 = 0
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact leafB20Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact leafB21Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 42)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact leafB22Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 41)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact leafB23Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 41)⁻¹ (by simp [zeroD1C1]) (values 42)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 41 = 0
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact leafB24Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact leafB25Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 42)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact leafB26Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) (values 41)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact leafB27Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) (values 41)⁻¹ (by simp [zeroD1C1]) (values 42)⁻¹ (by simp [zeroD1C2])

/-- Recursive exhaustion of chart `b4`. -/
theorem nodeB4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  by_cases zeroD1C0 : values 40 = 0
  ·
    by_cases zeroD1C1 : values 41 = 0
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact leafB40Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact nodeB41Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 42)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact nodeB42Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 41)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact nodeB43Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 41)⁻¹ (by simp [zeroD1C1]) (values 42)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 41 = 0
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact leafB44Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact leafB45Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 42)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact nodeB46Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) (values 41)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact nodeB47Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) (values 41)⁻¹ (by simp [zeroD1C1]) (values 42)⁻¹ (by simp [zeroD1C2])

/-- Recursive exhaustion of chart `b6`. -/
theorem nodeB6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  by_cases zeroD1C0 : values 40 = 0
  ·
    by_cases zeroD1C1 : values 41 = 0
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact leafB60Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact nodeB61Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 42)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact nodeB62Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 41)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact nodeB63Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 41)⁻¹ (by simp [zeroD1C1]) (values 42)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 41 = 0
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact leafB64Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact leafB65Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 42)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact nodeB66Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) (values 41)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact nodeB67Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) (values 41)⁻¹ (by simp [zeroD1C1]) (values 42)⁻¹ (by simp [zeroD1C2])

/-- Recursive exhaustion of chart `root`. -/
theorem rootImpossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : RootCommonZero values)
    : False := by
  by_cases zeroD0C0 : values 0 = 0
  ·
    by_cases zeroD0C1 : values 1 = 0
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact nodeB0Impossible values rootZero zeroD0C0 zeroD0C1 zeroD0C2
      · exact leafB1Impossible values rootZero zeroD0C0 zeroD0C1 (values 2)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact nodeB2Impossible values rootZero zeroD0C0 (values 1)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      · exact leafB3Impossible values rootZero zeroD0C0 (values 1)⁻¹ (by simp [zeroD0C1]) (values 2)⁻¹ (by simp [zeroD0C2])
  ·
    by_cases zeroD0C1 : values 1 = 0
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact nodeB4Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 zeroD0C2
      · exact leafB5Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 (values 2)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact nodeB6Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 1)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      · exact leafB7Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 1)⁻¹ (by simp [zeroD0C1]) (values 2)⁻¹ (by simp [zeroD0C2])

/-- The complete frozen component-57 carrier tree has no
common zero over any characteristic-zero field. -/
theorem component57HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R) :
    ¬ RootCommonZero values := by
  intro rootZero
  exact rootImpossible values rootZero

#print axioms Krenn.Component57.Tree.component57HasNoCommonZero

end Krenn.Component57.Tree
