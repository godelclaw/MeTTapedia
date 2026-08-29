import KrennComponent39.Root
import KrennComponent39.SelectedLeafB4_2_7_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component39.SelectedBridgeB4_2_7_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_2_7_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component39.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
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
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    (d3Equation0 : values 23 = 0)
    (d3Equation1 : values 25 = 0)
    (d3Equation2 : values 28 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 63 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d2Inverse0
    else if at1 : index.val = 64 then
      d2Inverse1
    else d2Inverse2
  let values4 : Fin 66 → R := values3
  apply Krenn.Component39.SelectedLeafB4_2_7_0.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨232, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨304, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨305, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨319, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨452, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨511, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨644, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨659, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1

#print axioms Krenn.Component39.SelectedBridgeB4_2_7_0.selectedLeafB4_2_7_0Impossible

end Krenn.Component39.SelectedBridgeB4_2_7_0
