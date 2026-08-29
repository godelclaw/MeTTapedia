import KrennComponent56.Root
import KrennComponent56.SelectedLeafB7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component56.SelectedBridgeB7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component56.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 57 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 57 then
      d0Inverse0
    else if at1 : index.val = 58 then
      d0Inverse1
    else d0Inverse2
  apply Krenn.Component56.SelectedLeafB7.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨212, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨254, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨263, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨274, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨372, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨373, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨377, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨379, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨382, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨397, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component56.SelectedBridgeB7.selectedLeafB7Impossible

end Krenn.Component56.SelectedBridgeB7
