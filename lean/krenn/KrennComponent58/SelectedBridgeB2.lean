import KrennComponent58.Root
import KrennComponent58.SelectedLeafB2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component58.SelectedBridgeB2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component58.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  apply Krenn.Component58.SelectedLeafB2.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨225, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨227, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨228, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨315, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨334, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨339, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨340, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨342, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨474, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨482, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨488, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨490, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨561, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨562, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨605, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component58.SelectedBridgeB2.selectedLeafB2Impossible

end Krenn.Component58.SelectedBridgeB2
