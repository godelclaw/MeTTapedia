import KrennComponent37.Root
import KrennComponent37.SelectedLeafB5_0_2_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component37.SelectedBridgeB5_0_2_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_0_2_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component37.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    (d3Equation0 : values 25 = 0)
    (d3Equation1 : values 27 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 30 * d3Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 64 → R := values1
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  let values4 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values3 ⟨index.val, inside⟩
    else d3Inverse2
  apply Krenn.Component37.SelectedLeafB5_0_2_1.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨295, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨298, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨299, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨307, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨317, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨393, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨410, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨411, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨446, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨482, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨487, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨505, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨510, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨519, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨646, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨656, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_0_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component37.SelectedBridgeB5_0_2_1.selectedLeafB5_0_2_1Impossible

end Krenn.Component37.SelectedBridgeB5_0_2_1
