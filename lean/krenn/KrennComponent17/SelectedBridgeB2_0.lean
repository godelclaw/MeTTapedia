import KrennComponent17.Root
import KrennComponent17.SelectedLeafB2_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component17.SelectedBridgeB2_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB2_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component17.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Equation1 : values 40 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 60 → R := values1
  apply Krenn.Component17.SelectedLeafB2_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨150, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨202, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨308, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨309, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨311, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨324, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨325, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨364, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨378, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨465, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨541, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨558, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨569, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨570, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨593, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨600, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component17.SelectedBridgeB2_0.selectedLeafB2_0Impossible

end Krenn.Component17.SelectedBridgeB2_0
