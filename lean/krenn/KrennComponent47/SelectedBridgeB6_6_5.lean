import KrennComponent47.Root
import KrennComponent47.SelectedLeafB6_6_5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component47.SelectedBridgeB6_6_5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_6_5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component47.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 52 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 53 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 54 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 58 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 58 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d2Inverse0
    else d2Inverse2
  apply Krenn.Component47.SelectedLeafB6_6_5.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨247, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨364, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨366, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨370, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨376, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨377, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨405, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨586, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB6_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component47.SelectedBridgeB6_6_5.selectedLeafB6_6_5Impossible

end Krenn.Component47.SelectedBridgeB6_6_5
