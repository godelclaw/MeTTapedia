import KrennComponent36.Root
import KrennComponent36.SelectedLeafB4_7_5_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component36.SelectedBridgeB4_7_5_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_7_5_7Impossible {R : Type*} [Field R] [CharZero R]
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
    (d1Inverse2 : R)
    (d1Equation2 : values 41 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 24 * d3Inverse0 - 1 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 26 * d3Inverse1 - 1 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 29 * d3Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else if at1 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 66 then
      d2Inverse0
    else d2Inverse2
  let values4 : Fin 71 → R := fun index =>
    if inside : index.val < 68 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 68 then
      d3Inverse0
    else if at1 : index.val = 69 then
      d3Inverse1
    else d3Inverse2
  apply Krenn.Component36.SelectedLeafB4_7_5_7.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_7_5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_7_5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_7_5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_7_5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1

#print axioms Krenn.Component36.SelectedBridgeB4_7_5_7.selectedLeafB4_7_5_7Impossible

end Krenn.Component36.SelectedBridgeB4_7_5_7
