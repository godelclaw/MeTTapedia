import KrennComponent39.Root
import KrennComponent39.SelectedLeafB0_2_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component39.SelectedBridgeB0_2_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_2_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component39.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 39 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 40 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 55 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 61 → R := values
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d2Inverse0
    else d2Inverse1
  apply Krenn.Component39.SelectedLeafB0_2_6.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨76, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨180, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨181, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨250, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨254, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨276, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨303, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨304, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨305, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨322, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨345, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨429, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨433, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨439, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨477, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨482, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨495, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨502, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨566, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨618, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨620, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨621, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨623, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨637, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨644, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨659, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨660, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component39.SelectedBridgeB0_2_6.selectedLeafB0_2_6Impossible

end Krenn.Component39.SelectedBridgeB0_2_6
