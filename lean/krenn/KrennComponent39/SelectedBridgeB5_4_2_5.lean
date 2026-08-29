import KrennComponent39.Root
import KrennComponent39.SelectedLeafB5_4_2_5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component39.SelectedBridgeB5_4_2_5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_4_2_5Impossible {R : Type*} [Field R] [CharZero R]
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
    (d1Equation2 : values 40 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 57 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 23 * d3Inverse0 - 1 = 0)
    (d3Equation1 : values 25 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 28 * d3Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  let values4 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d3Inverse0
    else d3Inverse2
  apply Krenn.Component39.SelectedLeafB5_4_2_5.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨180, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨181, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨188, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨197, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨277, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨303, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨304, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨305, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨319, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨342, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨365, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨397, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨419, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨422, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨430, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨439, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨470, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨536, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨570, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨619, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨630, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨633, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨659, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨660, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB5_4_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component39.SelectedBridgeB5_4_2_5.selectedLeafB5_4_2_5Impossible

end Krenn.Component39.SelectedBridgeB5_4_2_5
