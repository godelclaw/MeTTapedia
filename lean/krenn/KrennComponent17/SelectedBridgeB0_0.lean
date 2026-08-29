import KrennComponent17.Root
import KrennComponent17.SelectedLeafB0_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component17.SelectedBridgeB0_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component17.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Equation1 : values 40 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  let values1 : Fin 59 → R := values
  let values2 : Fin 59 → R := values1
  apply Krenn.Component17.SelectedLeafB0_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨214, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨215, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨311, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨325, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨351, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨373, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨436, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨441, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨486, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨505, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨541, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨549, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨550, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨553, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨567, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨568, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨572, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨599, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component17.Root.rootEquations, Krenn.Component17.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component17.SelectedBridgeB0_0.selectedLeafB0_0Impossible

end Krenn.Component17.SelectedBridgeB0_0
