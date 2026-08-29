import KrennComponent24.Root
import KrennComponent24.SelectedLeafB7_6_2_6_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component24.SelectedBridgeB7_6_2_6_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB7_6_2_6_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component24.Root.RootCommonZero values)
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
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 26 * d3Inverse0 - 1 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 28 * d3Inverse1 - 1 = 0)
    (d3Equation2 : values 31 = 0)
    (d4Equation0 : values 59 = 0)
    (d4Equation1 : values 60 = 0)
    (d4Equation2 : values 61 = 0)
    : False := by
  let values1 : Fin 65 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else if at1 : index.val = 63 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 67 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  let values4 : Fin 70 → R := fun index =>
    if inside : index.val < 68 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 68 then
      d3Inverse0
    else d3Inverse1
  let values5 : Fin 70 → R := values4
  apply Krenn.Component24.SelectedLeafB7_6_2_6_0.selectedHasNoCommonZero values5
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_6_2_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨503, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_6_2_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨516, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_6_2_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB7_6_2_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d4Equation1

#print axioms Krenn.Component24.SelectedBridgeB7_6_2_6_0.selectedLeafB7_6_2_6_0Impossible

end Krenn.Component24.SelectedBridgeB7_6_2_6_0
