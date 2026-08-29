import KrennComponent55.Root
import KrennComponent55.SelectedLeafB6_2_5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component55.SelectedBridgeB6_2_5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_2_5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component55.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 52 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 53 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 54 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 58 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 58 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d2Inverse0
    else d2Inverse2
  apply Krenn.Component55.SelectedLeafB6_2_5.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨217, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨223, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨225, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨228, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨232, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨234, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨257, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨296, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨341, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨342, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨345, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨354, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨390, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨490, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨512, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB6_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1

#print axioms Krenn.Component55.SelectedBridgeB6_2_5.selectedLeafB6_2_5Impossible

end Krenn.Component55.SelectedBridgeB6_2_5
