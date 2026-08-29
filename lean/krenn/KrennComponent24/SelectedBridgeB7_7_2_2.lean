import KrennComponent24.Root
import KrennComponent24.SelectedLeafB7_7_2_2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component24.SelectedBridgeB7_7_2_2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB7_7_2_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component24.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 41 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 43 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    (d3Equation0 : values 26 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 28 * d3Inverse1 - 1 = 0)
    (d3Equation2 : values 31 = 0)
    : False := by
  let values1 : Fin 65 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else if at1 : index.val = 63 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 68 → R := fun index =>
    if inside : index.val < 65 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d1Inverse0
    else if at1 : index.val = 66 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 69 → R := fun index =>
    if inside : index.val < 68 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  let values4 : Fin 70 → R := fun index =>
    if inside : index.val < 69 then
      values3 ⟨index.val, inside⟩
    else d3Inverse1
  apply Krenn.Component24.SelectedLeafB7_7_2_2.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨299, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨307, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨323, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨328, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨429, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨430, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨452, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨457, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨503, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨504, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨663, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_7_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component24.SelectedBridgeB7_7_2_2.selectedLeafB7_7_2_2Impossible

end Krenn.Component24.SelectedBridgeB7_7_2_2
