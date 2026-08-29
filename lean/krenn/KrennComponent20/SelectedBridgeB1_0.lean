import KrennComponent20.Root
import KrennComponent20.SelectedLeafB1_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component20.SelectedBridgeB1_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB1_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component20.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Equation1 : values 40 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 61 → R := values1
  apply Krenn.Component20.SelectedLeafB1_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨183, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨188, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨199, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨317, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨364, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨369, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨437, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨484, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨506, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨591, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨598, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨621, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨635, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component20.SelectedBridgeB1_0.selectedLeafB1_0Impossible

end Krenn.Component20.SelectedBridgeB1_0
