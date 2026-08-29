import KrennComponent10.Root
import KrennComponent10.SelectedLeafB6_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component10.SelectedBridgeB6_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
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
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d1Inverse0
    else if at1 : index.val = 63 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component10.SelectedLeafB6_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨68, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨165, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨186, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨364, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨406, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨409, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨446, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨550, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨628, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨634, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component10.SelectedBridgeB6_7.selectedLeafB6_7Impossible

end Krenn.Component10.SelectedBridgeB6_7
