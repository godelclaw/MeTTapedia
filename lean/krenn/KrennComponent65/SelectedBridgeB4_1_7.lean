import KrennComponent65.Root
import KrennComponent65.SelectedLeafB4_1_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component65.SelectedBridgeB4_1_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_1_7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component65.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Equation1 : values 39 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 40 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 55 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 63 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d2Inverse0
    else if at1 : index.val = 64 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component65.SelectedLeafB4_1_7.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨317, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨411, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨412, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨444, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨447, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component65.SelectedBridgeB4_1_7.selectedLeafB4_1_7Impossible

end Krenn.Component65.SelectedBridgeB4_1_7
