import KrennComponent62.Root
import KrennComponent62.SelectedLeafB0_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component62.SelectedBridgeB0_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component62.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 37 = 0)
    (d1Equation1 : values 38 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 39 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 60 → R := values
  let values2 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.Component62.SelectedLeafB0_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨470, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨646, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component62.SelectedBridgeB0_1.selectedLeafB0_1Impossible

end Krenn.Component62.SelectedBridgeB0_1
