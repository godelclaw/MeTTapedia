import KrennComponent62.Root
import KrennComponent62.SelectedLeafB6_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component62.SelectedBridgeB6_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component62.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 37 = 0)
    (d1Equation1 : values 38 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 39 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.Component62.SelectedLeafB6_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨97, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨128, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨129, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨130, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨131, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨133, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨135, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨137, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨138, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨140, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨151, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨158, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨186, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨226, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨243, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨299, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨309, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨315, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨321, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨390, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨407, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨435, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨436, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨439, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨473, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨491, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨549, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨558, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨559, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨578, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨598, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨619, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨631, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨649, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨650, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component62.SelectedBridgeB6_1.selectedLeafB6_1Impossible

end Krenn.Component62.SelectedBridgeB6_1
