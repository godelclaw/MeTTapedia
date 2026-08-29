import KrennComponent18.Root
import KrennComponent18.SelectedLeafB5_2_3_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component18.SelectedBridgeB5_2_3_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_2_3_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component18.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 41 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 43 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    (d3Equation0 : values 25 = 0)
    (d3Equation1 : values 28 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 31 * d3Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else d0Inverse2
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
  let values4 : Fin 67 → R := fun index =>
    if inside : index.val < 66 then
      values3 ⟨index.val, inside⟩
    else d3Inverse2
  apply Krenn.Component18.SelectedLeafB5_2_3_1.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨142, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨246, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨295, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨303, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨317, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨323, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨409, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨424, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨437, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨457, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨498, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨519, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨591, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨629, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0

#print axioms Krenn.Component18.SelectedBridgeB5_2_3_1.selectedLeafB5_2_3_1Impossible

end Krenn.Component18.SelectedBridgeB5_2_3_1
