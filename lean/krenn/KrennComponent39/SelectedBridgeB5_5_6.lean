import KrennComponent39.Root
import KrennComponent39.SelectedLeafB5_5_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component39.SelectedBridgeB5_5_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_5_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component39.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 38 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 39 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 40 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 55 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse2
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse0
    else d2Inverse1
  apply Krenn.Component39.SelectedLeafB5_5_6.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨95, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨181, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨188, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨195, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨197, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨248, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨268, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨277, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨282, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨303, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨304, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨305, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨313, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨319, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨324, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨342, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨396, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨397, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨398, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨410, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨419, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨422, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨430, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨439, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨445, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨452, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨470, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨477, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨503, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨542, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨566, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨570, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨659, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨660, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component39.SelectedBridgeB5_5_6.selectedLeafB5_5_6Impossible

end Krenn.Component39.SelectedBridgeB5_5_6
