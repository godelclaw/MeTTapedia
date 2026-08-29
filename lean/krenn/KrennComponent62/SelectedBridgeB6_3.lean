import KrennComponent62.Root
import KrennComponent62.SelectedLeafB6_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component62.SelectedBridgeB6_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component62.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 37 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 38 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 39 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component62.SelectedLeafB6_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨128, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨129, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨130, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨133, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨134, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨135, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨137, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨138, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨186, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨260, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨322, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨453, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨578, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨579, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨588, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨619, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component62.SelectedBridgeB6_3.selectedLeafB6_3Impossible

end Krenn.Component62.SelectedBridgeB6_3
