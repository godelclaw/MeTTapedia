import KrennComponent17.Root
import KrennComponent17.SelectedLeafB4_4_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component17.SelectedBridgeB4_4_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_4_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component17.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 40 = 0)
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
    else d0Inverse0
  let values2 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  let values3 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component17.SelectedLeafB4_4_3.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨60, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨183, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨202, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨206, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨285, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨306, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨307, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨311, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨323, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨325, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨327, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨330, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨415, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨423, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨430, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨436, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨441, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨459, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨505, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨541, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨572, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB4_4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component17.SelectedBridgeB4_4_3.selectedLeafB4_4_3Impossible

end Krenn.Component17.SelectedBridgeB4_4_3
