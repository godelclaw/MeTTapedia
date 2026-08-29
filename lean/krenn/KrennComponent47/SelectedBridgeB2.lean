import KrennComponent47.Root
import KrennComponent47.SelectedLeafB2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component47.SelectedBridgeB2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component47.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  let values1 : Fin 59 → R := fun index =>
    if inside : index.val < 58 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  apply Krenn.Component47.SelectedLeafB2.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨250, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨251, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨252, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨257, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨272, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨366, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨376, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨377, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨586, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component47.SelectedBridgeB2.selectedLeafB2Impossible

end Krenn.Component47.SelectedBridgeB2
