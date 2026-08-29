import KrennComponent25.Root
import KrennComponent25.SelectedLeafB0_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component25.SelectedBridgeB0_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component25.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  let values1 : Fin 61 → R := values
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.Component25.SelectedLeafB0_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨157, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨175, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨177, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨267, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨293, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨322, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨435, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨439, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨469, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component25.SelectedBridgeB0_6.selectedLeafB0_6Impossible

end Krenn.Component25.SelectedBridgeB0_6
