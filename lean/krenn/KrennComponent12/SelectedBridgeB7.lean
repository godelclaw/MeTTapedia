import KrennComponent12.Root
import KrennComponent12.SelectedLeafB7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component12.SelectedBridgeB7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component12.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d0Inverse0
    else if at1 : index.val = 60 then
      d0Inverse1
    else d0Inverse2
  apply Krenn.Component12.SelectedLeafB7.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨209, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨227, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨292, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨309, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨338, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨339, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨340, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨489, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨549, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨565, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component12.SelectedBridgeB7.selectedLeafB7Impossible

end Krenn.Component12.SelectedBridgeB7
