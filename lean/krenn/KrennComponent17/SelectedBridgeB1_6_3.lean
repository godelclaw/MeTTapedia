import KrennComponent17.Root
import KrennComponent17.SelectedLeafB1_6_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component17.SelectedBridgeB1_6_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB1_6_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component17.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
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
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component17.SelectedLeafB1_6_3.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB1_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨206, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB1_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨330, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB1_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨410, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB1_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨432, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB1_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨445, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB1_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB1_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨459, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB1_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨481, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB1_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨506, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB1_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨549, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB1_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨550, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB1_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨572, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB1_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB1_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB1_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component17.SelectedBridgeB1_6_3.selectedLeafB1_6_3Impossible

end Krenn.Component17.SelectedBridgeB1_6_3
