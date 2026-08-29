import KrennComponent24.Root
import KrennComponent24.SelectedLeafB0_5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component24.SelectedBridgeB0_5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component24.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 41 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 42 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 43 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := values
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.Component24.SelectedLeafB0_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨148, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨153, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨259, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨260, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨282, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨307, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨323, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨333, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨417, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨430, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨441, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨457, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨484, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨488, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨571, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨597, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨663, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

#print axioms Krenn.Component24.SelectedBridgeB0_5.selectedLeafB0_5Impossible

end Krenn.Component24.SelectedBridgeB0_5
