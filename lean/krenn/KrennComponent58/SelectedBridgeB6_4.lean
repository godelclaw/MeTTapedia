import KrennComponent58.Root
import KrennComponent58.SelectedLeafB6_4

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component58.SelectedBridgeB6_4

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component58.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 38 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 39 = 0)
    (d1Equation2 : values 40 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.Component58.SelectedLeafB6_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨225, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨227, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨253, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨339, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨340, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨342, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨474, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨561, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component58.SelectedBridgeB6_4.selectedLeafB6_4Impossible

end Krenn.Component58.SelectedBridgeB6_4
