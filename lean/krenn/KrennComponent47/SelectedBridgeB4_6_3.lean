import KrennComponent47.Root
import KrennComponent47.SelectedLeafB4_6_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component47.SelectedBridgeB4_6_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_6_3Impossible {R : Type*} [Field R] [CharZero R]
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
    (d1Equation2 : values 41 = 0)
    (d2Equation0 : values 52 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 53 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 54 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 59 → R := fun index =>
    if inside : index.val < 58 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 61 → R := fun index =>
    if inside : index.val < 59 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component47.SelectedLeafB4_6_3.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨224, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨272, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨287, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨364, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨376, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨377, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨381, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨506, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨586, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component47.SelectedBridgeB4_6_3.selectedLeafB4_6_3Impossible

end Krenn.Component47.SelectedBridgeB4_6_3
