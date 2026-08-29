import KrennComponent62.Root
import KrennComponent62.SelectedLeafB4_2_5_5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component62.SelectedBridgeB4_2_5_5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_2_5_5Impossible {R : Type*} [Field R] [CharZero R]
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
    (d2Inverse0 : R)
    (d2Equation0 : values 54 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 55 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 56 * d2Inverse2 - 1 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 23 * d3Inverse0 - 1 = 0)
    (d3Equation1 : values 26 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 27 * d3Inverse2 - 1 = 0)
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
      d2Inverse0
    else d2Inverse2
  let values4 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d3Inverse0
    else d3Inverse2
  apply Krenn.Component62.SelectedLeafB4_2_5_5.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨135, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨137, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨150, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨151, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨153, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨158, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨224, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨252, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨311, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨390, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨408, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨441, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨444, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨598, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_2_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component62.SelectedBridgeB4_2_5_5.selectedLeafB4_2_5_5Impossible

end Krenn.Component62.SelectedBridgeB4_2_5_5
