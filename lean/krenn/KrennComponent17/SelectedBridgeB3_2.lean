import KrennComponent17.Root
import KrennComponent17.SelectedLeafB3_2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component17.SelectedBridgeB3_2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB3_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component17.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.Component17.SelectedLeafB3_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨206, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨306, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨311, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨325, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨338, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨378, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨410, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨432, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨445, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨459, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨481, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨506, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨541, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨549, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨550, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨572, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component17.SelectedBridgeB3_2.selectedLeafB3_2Impossible

end Krenn.Component17.SelectedBridgeB3_2
