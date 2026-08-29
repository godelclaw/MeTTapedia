import KrennComponent39.Root
import KrennComponent39.SelectedLeafB7_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component39.SelectedBridgeB7_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB7_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component39.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Equation1 : values 39 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 40 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else if at1 : index.val = 62 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.Component39.SelectedLeafB7_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨268, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨304, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨305, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨313, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨416, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨422, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨423, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨439, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨441, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨465, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨537, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨555, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨644, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨649, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨659, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component39.SelectedBridgeB7_1.selectedLeafB7_1Impossible

end Krenn.Component39.SelectedBridgeB7_1
