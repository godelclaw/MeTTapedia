import KrennComponent24.Root
import KrennComponent24.SelectedLeafB5_6_6_4

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component24.SelectedBridgeB5_6_6_4

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_6_6_4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component24.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 41 * d1Inverse0 - 1 = 0)
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
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 66 then
      d2Inverse0
    else d2Inverse1
  let values4 : Fin 69 → R := fun index =>
    if inside : index.val < 68 then
      values3 ⟨index.val, inside⟩
    else d3Inverse0
  apply Krenn.Component24.SelectedLeafB5_6_6_4.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_6_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_6_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_6_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_6_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_6_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0

#print axioms Krenn.Component24.SelectedBridgeB5_6_6_4.selectedLeafB5_6_6_4Impossible

end Krenn.Component24.SelectedBridgeB5_6_6_4
