import KrennComponent37.Root
import KrennComponent37.SelectedLeafB4_2_7_2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component37.SelectedBridgeB4_2_7_2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_2_7_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component37.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    (d3Equation0 : values 25 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 27 * d3Inverse1 - 1 = 0)
    (d3Equation2 : values 30 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d2Inverse0
    else if at1 : index.val = 65 then
      d2Inverse1
    else d2Inverse2
  let values4 : Fin 68 → R := fun index =>
    if inside : index.val < 67 then
      values3 ⟨index.val, inside⟩
    else d3Inverse1
  apply Krenn.Component37.SelectedLeafB4_2_7_2.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨180, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨181, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨311, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨411, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨433, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨566, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨650, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB4_2_7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component37.SelectedBridgeB4_2_7_2.selectedLeafB4_2_7_2Impossible

end Krenn.Component37.SelectedBridgeB4_2_7_2
