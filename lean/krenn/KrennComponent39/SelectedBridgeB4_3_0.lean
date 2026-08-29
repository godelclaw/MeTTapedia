import KrennComponent39.Root
import KrennComponent39.SelectedLeafB4_3_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component39.SelectedBridgeB4_3_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_3_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component39.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 39 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 40 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Equation1 : values 56 = 0)
    (d2Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 64 → R := values2
  apply Krenn.Component39.SelectedLeafB4_3_0.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨188, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨197, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨250, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨268, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨304, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨305, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨313, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨317, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨369, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨382, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨417, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨419, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨433, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨439, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨479, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨542, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨563, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨659, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨660, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component39.SelectedBridgeB4_3_0.selectedLeafB4_3_0Impossible

end Krenn.Component39.SelectedBridgeB4_3_0
