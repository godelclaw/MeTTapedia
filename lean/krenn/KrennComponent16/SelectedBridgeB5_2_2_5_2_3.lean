import KrennComponent16.Root
import KrennComponent16.SelectedLeafB5_2_2_5_2_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component16.SelectedBridgeB5_2_2_5_2_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_2_2_5_2_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component16.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 41 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 43 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 26 * d3Inverse0 - 1 = 0)
    (d3Equation1 : values 28 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 31 * d3Inverse2 - 1 = 0)
    (d4Equation0 : values 59 = 0)
    (d4Inverse1 : R)
    (d4Equation1 : values 60 * d4Inverse1 - 1 = 0)
    (d4Equation2 : values 61 = 0)
    (d5Equation0 : values 3 = 0)
    (d5Inverse1 : R)
    (d5Equation1 : values 4 * d5Inverse1 - 1 = 0)
    (d5Inverse2 : R)
    (d5Equation2 : values 5 * d5Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  let values4 : Fin 68 → R := fun index =>
    if inside : index.val < 66 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 66 then
      d3Inverse0
    else d3Inverse2
  let values5 : Fin 69 → R := fun index =>
    if inside : index.val < 68 then
      values4 ⟨index.val, inside⟩
    else d4Inverse1
  let values6 : Fin 71 → R := fun index =>
    if inside : index.val < 69 then
      values5 ⟨index.val, inside⟩
    else if at0 : index.val = 69 then
      d5Inverse1
    else d5Inverse2
  apply Krenn.Component16.SelectedLeafB5_2_2_5_2_3.selectedHasNoCommonZero values6
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, values6, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_2_5_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, values6, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_2_5_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, values6, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_2_5_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, values6, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_2_5_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, values6, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_2_5_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, values6, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_2_5_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, values6, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_2_5_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨513, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, values6, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_2_5_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, values6, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_2_5_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, values6, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_2_5_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, values6, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_2_5_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, values6, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_2_5_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d4Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, values6, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_2_5_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d5Equation1

#print axioms Krenn.Component16.SelectedBridgeB5_2_2_5_2_3.selectedLeafB5_2_2_5_2_3Impossible

end Krenn.Component16.SelectedBridgeB5_2_2_5_2_3
