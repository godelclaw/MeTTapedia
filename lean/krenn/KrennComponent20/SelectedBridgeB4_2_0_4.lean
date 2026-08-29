import KrennComponent20.Root
import KrennComponent20.SelectedLeafB4_2_0_4

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component20.SelectedBridgeB4_2_0_4

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_2_0_4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component20.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Equation0 : values 54 = 0)
    (d2Equation1 : values 55 = 0)
    (d2Equation2 : values 56 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 25 * d3Inverse0 - 1 = 0)
    (d3Equation1 : values 27 = 0)
    (d3Equation2 : values 29 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 62 → R := values2
  let values4 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values3 ⟨index.val, inside⟩
    else d3Inverse0
  apply Krenn.Component20.SelectedLeafB4_2_0_4.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨186, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨188, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨551, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨635, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component20.SelectedBridgeB4_2_0_4.selectedLeafB4_2_0_4Impossible

end Krenn.Component20.SelectedBridgeB4_2_0_4
