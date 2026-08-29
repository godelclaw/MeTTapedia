import KrennComponent46.Root
import KrennComponent46.SelectedLeafB3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component46.SelectedBridgeB3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component46.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse1
    else d0Inverse2
  apply Krenn.Component46.SelectedLeafB3.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨43, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨216, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨220, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨229, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component46.SelectedBridgeB3.selectedLeafB3Impossible

end Krenn.Component46.SelectedBridgeB3
