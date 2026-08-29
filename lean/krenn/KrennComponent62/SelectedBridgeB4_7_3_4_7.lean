import KrennComponent62.Root
import KrennComponent62.SelectedLeafB4_7_3_4_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component62.SelectedBridgeB4_7_3_4_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_7_3_4_7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component62.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 37 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 38 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 39 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 54 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 55 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 56 * d2Inverse2 - 1 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 23 * d3Inverse0 - 1 = 0)
    (d3Equation1 : values 26 = 0)
    (d3Equation2 : values 27 = 0)
    (d4Inverse0 : R)
    (d4Equation0 : values 57 * d4Inverse0 - 1 = 0)
    (d4Inverse1 : R)
    (d4Equation1 : values 58 * d4Inverse1 - 1 = 0)
    (d4Inverse2 : R)
    (d4Equation2 : values 59 * d4Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d1Inverse0
    else if at1 : index.val = 62 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d2Inverse1
    else d2Inverse2
  let values4 : Fin 67 → R := fun index =>
    if inside : index.val < 66 then
      values3 ⟨index.val, inside⟩
    else d3Inverse0
  let values5 : Fin 70 → R := fun index =>
    if inside : index.val < 67 then
      values4 ⟨index.val, inside⟩
    else if at0 : index.val = 67 then
      d4Inverse0
    else if at1 : index.val = 68 then
      d4Inverse1
    else d4Inverse2
  apply Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedHasNoCommonZero values5
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨135, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨146, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨153, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨295, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨370, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨588, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨589, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨619, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d4Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_7_3_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d4Equation1

#print axioms Krenn.Component62.SelectedBridgeB4_7_3_4_7.selectedLeafB4_7_3_4_7Impossible

end Krenn.Component62.SelectedBridgeB4_7_3_4_7
