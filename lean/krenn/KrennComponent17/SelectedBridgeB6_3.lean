import KrennComponent17.Root
import KrennComponent17.SelectedLeafB6_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component17.SelectedBridgeB6_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component17.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 41 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component17.SelectedLeafB6_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨42, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨213, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨311, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨323, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨324, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨325, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨335, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨400, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨415, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨441, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨541, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨558, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨567, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨568, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨599, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component17.SelectedBridgeB6_3.selectedLeafB6_3Impossible

end Krenn.Component17.SelectedBridgeB6_3
