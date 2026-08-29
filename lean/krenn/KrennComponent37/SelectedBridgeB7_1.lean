import KrennComponent37.Root
import KrennComponent37.SelectedLeafB7_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component37.SelectedBridgeB7_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB7_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component37.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 65 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else if at1 : index.val = 63 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.Component37.SelectedLeafB7_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨42, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨122, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨142, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨147, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨175, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨182, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨287, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨296, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨298, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨299, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨303, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨315, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨319, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨364, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨374, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨402, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨410, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨430, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨435, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨442, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨447, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨453, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨470, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨487, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨499, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨526, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨529, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨572, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨590, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨605, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨614, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨645, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨647, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨648, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨656, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component37.SelectedBridgeB7_1.selectedLeafB7_1Impossible

end Krenn.Component37.SelectedBridgeB7_1
