import KrennComponent59.Root
import KrennComponent59.SelectedLeafB4_5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component59.SelectedBridgeB4_5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component59.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 36 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 37 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 38 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 59 → R := fun index =>
    if inside : index.val < 58 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 61 → R := fun index =>
    if inside : index.val < 59 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.Component59.SelectedLeafB4_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨216, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨220, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨338, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨341, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨426, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨441, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨497, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨498, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨559, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component59.Root.rootEquations, Krenn.Component59.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

#print axioms Krenn.Component59.SelectedBridgeB4_5.selectedLeafB4_5Impossible

end Krenn.Component59.SelectedBridgeB4_5
