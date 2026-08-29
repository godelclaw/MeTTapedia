import KrennComponent17.Root
import KrennComponent17.SelectedLeafB2_2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component17.SelectedBridgeB2_2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB2_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component17.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.Component17.SelectedLeafB2_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨212, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨311, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨325, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨372, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨414, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨424, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨441, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨445, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨459, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨465, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨541, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨549, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨572, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component17.SelectedBridgeB2_2.selectedLeafB2_2Impossible

end Krenn.Component17.SelectedBridgeB2_2
