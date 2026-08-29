import KrennComponent62.Root
import KrennComponent62.SelectedLeafB4_2_3_4_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component62.SelectedBridgeB4_2_3_4_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_2_3_4_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component62.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 37 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 38 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 39 = 0)
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
    (d4Equation2 : values 59 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d2Inverse1
    else d2Inverse2
  let values4 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values3 ⟨index.val, inside⟩
    else d3Inverse0
  let values5 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values4 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d4Inverse0
    else d4Inverse1
  apply Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedHasNoCommonZero values5
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨146, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨147, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨153, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨154, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨293, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨296, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨311, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨404, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨408, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨444, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨453, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨476, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨484, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨550, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨578, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d4Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_3_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d4Equation2

#print axioms Krenn.Component62.SelectedBridgeB4_2_3_4_6.selectedLeafB4_2_3_4_6Impossible

end Krenn.Component62.SelectedBridgeB4_2_3_4_6
