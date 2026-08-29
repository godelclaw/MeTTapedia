import KrennComponent12.Root
import KrennComponent12.SelectedLeafB6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component12.SelectedBridgeB6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component12.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d0Inverse0
    else d0Inverse1
  apply Krenn.Component12.SelectedLeafB6.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨149, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨201, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨202, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨209, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨292, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨309, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨338, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨339, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨340, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨405, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨407, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨485, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨486, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨549, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨561, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component12.SelectedBridgeB6.selectedLeafB6Impossible

end Krenn.Component12.SelectedBridgeB6
