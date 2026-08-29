import KrennComponent1.Root
import KrennComponent1.SelectedLeafB4_4_5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component1.SelectedBridgeB4_4_5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_4_5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 51 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 52 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 53 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 58 → R := fun index =>
    if inside : index.val < 57 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 59 → R := fun index =>
    if inside : index.val < 58 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  let values3 : Fin 61 → R := fun index =>
    if inside : index.val < 59 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d2Inverse0
    else d2Inverse2
  apply Krenn.Component1.SelectedLeafB4_4_5.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨261, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨366, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨384, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨385, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨413, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨503, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨545, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0

#print axioms Krenn.Component1.SelectedBridgeB4_4_5.selectedLeafB4_4_5Impossible

end Krenn.Component1.SelectedBridgeB4_4_5
