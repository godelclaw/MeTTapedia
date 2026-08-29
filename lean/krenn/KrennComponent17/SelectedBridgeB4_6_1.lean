import KrennComponent17.Root
import KrennComponent17.SelectedLeafB4_6_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component17.SelectedBridgeB4_6_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_6_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component17.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Equation0 : values 53 = 0)
    (d2Equation1 : values 54 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 55 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component17.SelectedLeafB4_6_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨40, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨89, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨208, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨281, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨308, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨309, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨311, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨323, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨325, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨428, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨430, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨435, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨441, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨445, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨501, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨520, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨569, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨570, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨600, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component17.SelectedBridgeB4_6_1.selectedLeafB4_6_1Impossible

end Krenn.Component17.SelectedBridgeB4_6_1
