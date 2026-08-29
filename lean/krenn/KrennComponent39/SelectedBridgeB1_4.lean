import KrennComponent39.Root
import KrennComponent39.SelectedLeafB1_4

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component39.SelectedBridgeB1_4

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB1_4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component39.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 38 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 39 = 0)
    (d1Equation2 : values 40 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.Component39.SelectedLeafB1_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨180, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨181, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨219, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨254, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨303, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨308, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨313, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨317, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨321, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨322, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨342, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨345, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨382, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨396, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨397, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨410, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨411, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨416, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨418, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨419, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨429, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨433, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨439, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨482, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨503, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨532, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨536, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨566, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨570, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨615, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨644, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨660, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component39.SelectedBridgeB1_4.selectedLeafB1_4Impossible

end Krenn.Component39.SelectedBridgeB1_4
