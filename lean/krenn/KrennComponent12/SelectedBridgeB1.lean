import KrennComponent12.Root
import KrennComponent12.SelectedLeafB1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component12.SelectedBridgeB1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component12.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  apply Krenn.Component12.SelectedLeafB1.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨209, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨216, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨218, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨227, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨292, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨339, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨400, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨489, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨578, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨579, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨605, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨611, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component12.SelectedBridgeB1.selectedLeafB1Impossible

end Krenn.Component12.SelectedBridgeB1
