import KrennComponent58.Root
import KrennComponent58.SelectedLeafB4_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component58.SelectedBridgeB4_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component58.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Equation1 : values 39 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 40 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.Component58.SelectedLeafB4_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨227, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨339, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨342, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨459, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨474, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨482, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨488, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨561, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨562, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component58.SelectedBridgeB4_1.selectedLeafB4_1Impossible

end Krenn.Component58.SelectedBridgeB4_1
