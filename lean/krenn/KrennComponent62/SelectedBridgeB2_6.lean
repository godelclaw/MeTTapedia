import KrennComponent62.Root
import KrennComponent62.SelectedLeafB2_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component62.SelectedBridgeB2_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB2_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component62.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 37 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 38 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 39 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.Component62.SelectedLeafB2_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨83, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨130, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨133, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨141, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨159, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨265, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨619, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component62.SelectedBridgeB2_6.selectedLeafB2_6Impossible

end Krenn.Component62.SelectedBridgeB2_6
