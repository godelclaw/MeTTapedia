import KrennComponent25.Root
import KrennComponent25.SelectedLeafB7_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component25.SelectedBridgeB7_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB7_7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component25.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 41 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else if at1 : index.val = 62 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 67 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else if at1 : index.val = 65 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component25.SelectedLeafB7_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨75, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨143, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨146, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨148, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨152, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨402, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨427, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨433, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨435, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨436, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨449, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨587, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨616, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨628, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component25.SelectedBridgeB7_7.selectedLeafB7_7Impossible

end Krenn.Component25.SelectedBridgeB7_7
