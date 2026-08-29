import KrennComponent19.Root
import KrennComponent19.SelectedLeafB5_2_6_5_5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component19.SelectedBridgeB5_2_6_5_5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_2_6_5_5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component19.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 42 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 43 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 44 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 26 * d3Inverse0 - 1 = 0)
    (d3Equation1 : values 29 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 32 * d3Inverse2 - 1 = 0)
    (d4Inverse0 : R)
    (d4Equation0 : values 59 * d4Inverse0 - 1 = 0)
    (d4Equation1 : values 60 = 0)
    (d4Inverse2 : R)
    (d4Equation2 : values 61 * d4Inverse2 - 1 = 0)
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
      d2Inverse0
    else d2Inverse1
  let values4 : Fin 69 → R := fun index =>
    if inside : index.val < 67 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 67 then
      d3Inverse0
    else d3Inverse2
  let values5 : Fin 71 → R := fun index =>
    if inside : index.val < 69 then
      values4 ⟨index.val, inside⟩
    else if at0 : index.val = 69 then
      d4Inverse0
    else d4Inverse2
  apply Krenn.Component19.SelectedLeafB5_2_6_5_5.selectedHasNoCommonZero values5
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_6_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_6_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨486, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_6_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_6_5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d4Equation1

#print axioms Krenn.Component19.SelectedBridgeB5_2_6_5_5.selectedLeafB5_2_6_5_5Impossible

end Krenn.Component19.SelectedBridgeB5_2_6_5_5
