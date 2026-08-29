import KrennComponent22.Root
import KrennComponent22.SelectedLeafB1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component22.SelectedBridgeB1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component22.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  apply Krenn.Component22.SelectedLeafB1.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨219, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨225, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨237, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨345, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨364, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨369, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨371, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨388, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨477, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨635, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component22.Root.rootEquations, Krenn.Component22.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component22.SelectedBridgeB1.selectedLeafB1Impossible

end Krenn.Component22.SelectedBridgeB1
