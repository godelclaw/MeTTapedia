import KrennComponent39.Root
import KrennComponent39.SelectedLeafB0_4_2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component39.SelectedBridgeB0_4_2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_4_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component39.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 38 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 39 = 0)
    (d1Equation2 : values 40 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 61 → R := values
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  let values3 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  apply Krenn.Component39.SelectedLeafB0_4_2.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨183, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨254, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨282, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨322, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨324, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨394, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨397, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨410, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨430, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨566, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨570, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨623, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨660, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB0_4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component39.SelectedBridgeB0_4_2.selectedLeafB0_4_2Impossible

end Krenn.Component39.SelectedBridgeB0_4_2
