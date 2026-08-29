import KrennComponent24.Root
import KrennComponent24.SelectedLeafB3_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component24.SelectedBridgeB3_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB3_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component24.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 41 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 43 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component24.SelectedLeafB3_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨153, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨322, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨357, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨368, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨461, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨488, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨509, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨571, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨614, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component24.SelectedBridgeB3_3.selectedLeafB3_3Impossible

end Krenn.Component24.SelectedBridgeB3_3
