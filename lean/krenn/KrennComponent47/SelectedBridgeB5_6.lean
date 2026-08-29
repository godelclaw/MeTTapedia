import KrennComponent47.Root
import KrennComponent47.SelectedLeafB5_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component47.SelectedBridgeB5_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component47.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 58 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 58 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.Component47.SelectedLeafB5_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨208, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨220, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨221, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨240, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨272, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨286, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨287, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨364, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨365, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨366, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨370, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨376, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨377, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨378, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨380, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨384, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨401, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨403, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨410, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨411, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨449, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨544, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨545, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨550, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨586, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component47.SelectedBridgeB5_6.selectedLeafB5_6Impossible

end Krenn.Component47.SelectedBridgeB5_6
