import KrennComponent16.Root
import KrennComponent16.SelectedLeafB5_2_3_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component16.SelectedBridgeB5_2_3_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_2_3_6Impossible {R : Type*} [Field R] [CharZero R]
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
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 26 * d3Inverse0 - 1 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 28 * d3Inverse1 - 1 = 0)
    (d3Equation2 : values 31 = 0)
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
  apply Krenn.Component16.SelectedLeafB5_2_3_6.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨142, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨148, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨366, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨436, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨448, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨571, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨588, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨595, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_2_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component16.SelectedBridgeB5_2_3_6.selectedLeafB5_2_3_6Impossible

end Krenn.Component16.SelectedBridgeB5_2_3_6
