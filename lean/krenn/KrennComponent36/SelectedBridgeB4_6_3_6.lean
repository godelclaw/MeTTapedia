import KrennComponent36.Root
import KrennComponent36.SelectedLeafB4_6_3_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component36.SelectedBridgeB4_6_3_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_6_3_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component36.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 24 * d3Inverse0 - 1 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 26 * d3Inverse1 - 1 = 0)
    (d3Equation2 : values 29 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse1
    else d2Inverse2
  let values4 : Fin 69 → R := fun index =>
    if inside : index.val < 67 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 67 then
      d3Inverse0
    else d3Inverse1
  apply Krenn.Component36.SelectedLeafB4_6_3_6.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨153, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨271, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨305, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨307, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨451, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨453, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨562, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨662, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component36.SelectedBridgeB4_6_3_6.selectedLeafB4_6_3_6Impossible

end Krenn.Component36.SelectedBridgeB4_6_3_6
