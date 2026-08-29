import KrennComponent18.Root
import KrennComponent18.SelectedLeafB0_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component18.SelectedBridgeB0_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component18.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 41 = 0)
    (d1Equation1 : values 42 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 43 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 61 → R := values
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.Component18.SelectedLeafB0_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨327, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨437, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨562, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component18.SelectedBridgeB0_1.selectedLeafB0_1Impossible

end Krenn.Component18.SelectedBridgeB0_1
