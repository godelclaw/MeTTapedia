import KrennComponent18.Root
import KrennComponent18.SelectedLeafB4_2_1_7_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component18.SelectedBridgeB4_2_1_7_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_2_1_7_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component18.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 41 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 43 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Equation1 : values 56 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 25 * d3Inverse0 - 1 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 28 * d3Inverse1 - 1 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 31 * d3Inverse2 - 1 = 0)
    (d4Inverse0 : R)
    (d4Equation0 : values 58 * d4Inverse0 - 1 = 0)
    (d4Inverse1 : R)
    (d4Equation1 : values 59 * d4Inverse1 - 1 = 0)
    (d4Equation2 : values 60 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  let values4 : Fin 67 → R := fun index =>
    if inside : index.val < 64 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d3Inverse0
    else if at1 : index.val = 65 then
      d3Inverse1
    else d3Inverse2
  let values5 : Fin 69 → R := fun index =>
    if inside : index.val < 67 then
      values4 ⟨index.val, inside⟩
    else if at0 : index.val = 67 then
      d4Inverse0
    else d4Inverse1
  apply Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedHasNoCommonZero values5
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨148, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨151, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨271, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨315, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨319, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨323, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨426, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨431, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨433, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨496, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨501, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨505, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨506, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨563, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨656, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d4Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_1_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d4Equation2

#print axioms Krenn.Component18.SelectedBridgeB4_2_1_7_6.selectedLeafB4_2_1_7_6Impossible

end Krenn.Component18.SelectedBridgeB4_2_1_7_6
