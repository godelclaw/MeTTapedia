import KrennComponent20.Root
import KrennComponent20.SelectedLeafB5_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component20.SelectedBridgeB5_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component20.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 41 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component20.SelectedLeafB5_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨97, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨141, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨177, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨183, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨186, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨197, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨291, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨313, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨317, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨345, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨351, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨369, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨373, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨374, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨387, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨408, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨527, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨534, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨551, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨579, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨622, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨634, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨635, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component20.SelectedBridgeB5_3.selectedLeafB5_3Impossible

end Krenn.Component20.SelectedBridgeB5_3
