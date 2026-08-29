import KrennComponent53.Root
import KrennComponent53.SelectedLeafB6_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component53.SelectedBridgeB6_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component53.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 41 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 43 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.Component53.SelectedLeafB6_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨174, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨200, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨201, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨204, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨205, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨214, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨228, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨230, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨244, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨246, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨247, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨355, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨357, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨394, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨411, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨477, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨491, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨558, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨559, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨570, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨622, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨635, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨636, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component53.SelectedBridgeB6_6.selectedLeafB6_6Impossible

end Krenn.Component53.SelectedBridgeB6_6
