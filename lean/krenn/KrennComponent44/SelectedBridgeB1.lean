import KrennComponent44.Root
import KrennComponent44.SelectedLeafB1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component44.SelectedBridgeB1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component44.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  apply Krenn.Component44.SelectedLeafB1.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨208, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨212, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨221, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨228, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨243, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨367, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨369, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨391, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0

#print axioms Krenn.Component44.SelectedBridgeB1.selectedLeafB1Impossible

end Krenn.Component44.SelectedBridgeB1
