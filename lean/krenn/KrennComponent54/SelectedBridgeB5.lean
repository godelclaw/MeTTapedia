import KrennComponent54.Root
import KrennComponent54.SelectedLeafB5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component54.SelectedBridgeB5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component54.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else d0Inverse2
  apply Krenn.Component54.SelectedLeafB5.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨204, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨214, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨364, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨366, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨383, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨384, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨473, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨638, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component54.SelectedBridgeB5.selectedLeafB5Impossible

end Krenn.Component54.SelectedBridgeB5
