import KrennComponent47.Root
import KrennComponent47.SelectedLeafB4_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component47.SelectedBridgeB4_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component47.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 41 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 59 → R := fun index =>
    if inside : index.val < 58 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 59 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d1Inverse0
    else if at1 : index.val = 60 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component47.SelectedLeafB4_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨40, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨208, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨219, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨243, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨245, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨246, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨252, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨272, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨287, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨368, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨374, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨376, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨377, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨459, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨499, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨537, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨548, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨549, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨567, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨569, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨573, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨586, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component47.SelectedBridgeB4_7.selectedLeafB4_7Impossible

end Krenn.Component47.SelectedBridgeB4_7
