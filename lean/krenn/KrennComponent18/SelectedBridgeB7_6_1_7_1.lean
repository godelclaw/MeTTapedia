import KrennComponent18.Root
import KrennComponent18.SelectedLeafB7_6_1_7_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component18.SelectedBridgeB7_6_1_7_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB7_6_1_7_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component18.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 41 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 43 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Equation1 : values 56 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 25 * d3Inverse0 - 1 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 28 * d3Inverse1 - 1 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 31 * d3Inverse2 - 1 = 0)
    (d4Equation0 : values 58 = 0)
    (d4Equation1 : values 59 = 0)
    (d4Inverse2 : R)
    (d4Equation2 : values 60 * d4Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else if at1 : index.val = 62 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  let values4 : Fin 70 → R := fun index =>
    if inside : index.val < 67 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 67 then
      d3Inverse0
    else if at1 : index.val = 68 then
      d3Inverse1
    else d3Inverse2
  let values5 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values4 ⟨index.val, inside⟩
    else d4Inverse2
  apply Krenn.Component18.SelectedLeafB7_6_1_7_1.selectedHasNoCommonZero values5
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_6_1_7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_6_1_7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨491, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_6_1_7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_6_1_7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d4Equation1

#print axioms Krenn.Component18.SelectedBridgeB7_6_1_7_1.selectedLeafB7_6_1_7_1Impossible

end Krenn.Component18.SelectedBridgeB7_6_1_7_1
