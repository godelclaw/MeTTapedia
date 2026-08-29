import KrennComponent62.Root
import KrennComponent62.SelectedLeafB0_7_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component62.SelectedBridgeB0_7_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_7_7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component62.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 37 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 38 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 39 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 54 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 55 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 56 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 60 → R := values
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 60 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d1Inverse0
    else if at1 : index.val = 61 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 63 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d2Inverse0
    else if at1 : index.val = 64 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component62.SelectedLeafB0_7_7.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨83, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨97, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨135, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨137, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨141, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨146, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨147, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨149, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨150, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨151, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨153, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨154, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨158, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨223, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨224, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨227, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨252, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨293, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨295, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨296, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨311, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨315, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨338, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨404, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨407, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨408, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨437, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨441, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨444, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨453, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨457, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨465, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨470, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨476, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨550, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨589, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨599, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1

#print axioms Krenn.Component62.SelectedBridgeB0_7_7.selectedLeafB0_7_7Impossible

end Krenn.Component62.SelectedBridgeB0_7_7
