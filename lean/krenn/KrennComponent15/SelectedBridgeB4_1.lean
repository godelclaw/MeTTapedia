import KrennComponent15.Root
import KrennComponent15.SelectedLeafB4_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component15.SelectedBridgeB4_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component15.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 36 = 0)
    (d1Equation1 : values 37 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 38 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 58 → R := fun index =>
    if inside : index.val < 57 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 59 → R := fun index =>
    if inside : index.val < 58 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.Component15.SelectedLeafB4_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨232, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨234, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨365, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨366, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨367, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨368, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨376, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨506, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨519, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨527, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨546, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component15.SelectedBridgeB4_1.selectedLeafB4_1Impossible

end Krenn.Component15.SelectedBridgeB4_1
