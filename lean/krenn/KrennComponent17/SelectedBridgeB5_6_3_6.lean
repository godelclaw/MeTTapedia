import KrennComponent17.Root
import KrennComponent17.SelectedLeafB5_6_3_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component17.SelectedBridgeB5_6_3_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_6_3_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component17.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Equation0 : values 53 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 54 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 55 * d2Inverse2 - 1 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 24 * d3Inverse0 - 1 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 26 * d3Inverse1 - 1 = 0)
    (d3Equation2 : values 29 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d2Inverse1
    else d2Inverse2
  let values4 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d3Inverse0
    else d3Inverse1
  apply Krenn.Component17.SelectedLeafB5_6_3_6.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨60, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨77, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨308, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨309, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨325, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨327, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨364, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨436, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨486, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨541, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨570, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨600, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component17.SelectedBridgeB5_6_3_6.selectedLeafB5_6_3_6Impossible

end Krenn.Component17.SelectedBridgeB5_6_3_6
