import KrennComponent18.Root
import KrennComponent18.SelectedLeafB5_2_1_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component18.SelectedBridgeB5_2_1_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_2_1_7Impossible {R : Type*} [Field R] [CharZero R]
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
    (d2Equation1 : values 56 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 25 * d3Inverse0 - 1 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 28 * d3Inverse1 - 1 = 0)
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
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  let values4 : Fin 68 → R := fun index =>
    if inside : index.val < 65 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d3Inverse0
    else if at1 : index.val = 66 then
      d3Inverse1
    else d3Inverse2
  apply Krenn.Component18.SelectedLeafB5_2_1_7.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨142, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨147, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨165, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨314, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨315, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨319, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨322, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨323, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨345, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨403, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨407, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨426, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨430, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨435, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨437, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨449, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨460, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨479, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨482, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨564, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨590, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨645, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨646, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨649, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB5_2_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component18.SelectedBridgeB5_2_1_7.selectedLeafB5_2_1_7Impossible

end Krenn.Component18.SelectedBridgeB5_2_1_7
