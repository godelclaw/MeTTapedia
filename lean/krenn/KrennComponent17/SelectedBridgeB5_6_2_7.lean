import KrennComponent17.Root
import KrennComponent17.SelectedLeafB5_6_2_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component17.SelectedBridgeB5_6_2_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_6_2_7Impossible {R : Type*} [Field R] [CharZero R]
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
    (d2Equation2 : values 55 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 24 * d3Inverse0 - 1 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 26 * d3Inverse1 - 1 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 29 * d3Inverse2 - 1 = 0)
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
  let values3 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  let values4 : Fin 67 → R := fun index =>
    if inside : index.val < 64 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d3Inverse0
    else if at1 : index.val = 65 then
      d3Inverse1
    else d3Inverse2
  apply Krenn.Component17.SelectedLeafB5_6_2_7.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨56, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨137, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨204, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨228, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨253, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨308, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨314, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨326, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨357, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨358, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨405, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨427, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨435, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨445, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨452, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨489, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨494, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨497, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨549, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨553, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨567, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨568, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨569, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨570, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨571, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨575, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨599, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨600, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB5_6_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component17.SelectedBridgeB5_6_2_7.selectedLeafB5_6_2_7Impossible

end Krenn.Component17.SelectedBridgeB5_6_2_7
