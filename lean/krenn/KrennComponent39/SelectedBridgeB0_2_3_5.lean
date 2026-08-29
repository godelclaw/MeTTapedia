import KrennComponent39.Root
import KrennComponent39.SelectedLeafB0_2_3_5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component39.SelectedBridgeB0_2_3_5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_2_3_5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component39.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 39 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 40 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 23 * d3Inverse0 - 1 = 0)
    (d3Equation1 : values 25 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 28 * d3Inverse2 - 1 = 0)
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
      d2Inverse1
    else d2Inverse2
  let values4 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d3Inverse0
    else d3Inverse2
  apply Krenn.Component39.SelectedLeafB0_2_3_5.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨180, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨181, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨195, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨250, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨277, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨282, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨303, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨313, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨317, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨319, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨321, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨322, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨324, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨345, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨367, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨382, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨396, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨399, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨413, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨416, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨418, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨419, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨423, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨430, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨439, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨465, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨470, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨482, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨497, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨535, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨566, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨570, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨591, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨644, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨651, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨660, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_2_3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component39.SelectedBridgeB0_2_3_5.selectedLeafB0_2_3_5Impossible

end Krenn.Component39.SelectedBridgeB0_2_3_5
