import KrennComponent59.Root
import KrennComponent59.SelectedLeafB4_7_5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component59.SelectedBridgeB4_7_5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_7_5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component59.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 36 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 37 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 38 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 52 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 53 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 54 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 59 → R := fun index =>
    if inside : index.val < 58 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 59 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d1Inverse0
    else if at1 : index.val = 60 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d2Inverse0
    else d2Inverse2
  apply Krenn.Component59.SelectedLeafB4_7_5.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component59.SelectedBridgeB4_7_5.selectedLeafB4_7_5Impossible

end Krenn.Component59.SelectedBridgeB4_7_5
