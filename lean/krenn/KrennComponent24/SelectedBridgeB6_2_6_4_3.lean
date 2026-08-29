import KrennComponent24.Root
import KrennComponent24.SelectedLeafB6_2_6_4_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component24.SelectedBridgeB6_2_6_4_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_2_6_4_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component24.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 41 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 43 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 26 * d3Inverse0 - 1 = 0)
    (d3Equation1 : values 28 = 0)
    (d3Equation2 : values 31 = 0)
    (d4Equation0 : values 59 = 0)
    (d4Inverse1 : R)
    (d4Equation1 : values 60 * d4Inverse1 - 1 = 0)
    (d4Inverse2 : R)
    (d4Equation2 : values 61 * d4Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse0
    else d2Inverse1
  let values4 : Fin 68 → R := fun index =>
    if inside : index.val < 67 then
      values3 ⟨index.val, inside⟩
    else d3Inverse0
  let values5 : Fin 70 → R := fun index =>
    if inside : index.val < 68 then
      values4 ⟨index.val, inside⟩
    else if at0 : index.val = 68 then
      d4Inverse1
    else d4Inverse2
  apply Krenn.Component24.SelectedLeafB6_2_6_4_3.selectedHasNoCommonZero values5
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_6_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_6_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_6_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨129, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_6_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨323, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_6_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_6_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨663, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_6_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_6_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_6_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_6_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_6_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_6_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d4Equation1

#print axioms Krenn.Component24.SelectedBridgeB6_2_6_4_3.selectedLeafB6_2_6_4_3Impossible

end Krenn.Component24.SelectedBridgeB6_2_6_4_3
