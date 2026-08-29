import KrennComponent65.Root
import KrennComponent65.SelectedLeafB6_7_1_4_4

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component65.SelectedBridgeB6_7_1_4_4

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_7_1_4_4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component65.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 38 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 39 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 40 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Equation1 : values 56 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 24 * d3Inverse0 - 1 = 0)
    (d3Equation1 : values 27 = 0)
    (d3Equation2 : values 28 = 0)
    (d4Inverse0 : R)
    (d4Equation0 : values 58 * d4Inverse0 - 1 = 0)
    (d4Equation1 : values 59 = 0)
    (d4Equation2 : values 60 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else if at1 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  let values4 : Fin 68 → R := fun index =>
    if inside : index.val < 67 then
      values3 ⟨index.val, inside⟩
    else d3Inverse0
  let values5 : Fin 69 → R := fun index =>
    if inside : index.val < 68 then
      values4 ⟨index.val, inside⟩
    else d4Inverse0
  apply Krenn.Component65.SelectedLeafB6_7_1_4_4.selectedHasNoCommonZero values5
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB6_7_1_4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨412, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB6_7_1_4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨447, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB6_7_1_4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB6_7_1_4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB6_7_1_4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB6_7_1_4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB6_7_1_4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d4Equation1

#print axioms Krenn.Component65.SelectedBridgeB6_7_1_4_4.selectedLeafB6_7_1_4_4Impossible

end Krenn.Component65.SelectedBridgeB6_7_1_4_4
