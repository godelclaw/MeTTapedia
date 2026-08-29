import KrennComponent14.Root
import KrennComponent14.SelectedLeafB6_2_4_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component14.SelectedBridgeB6_2_4_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_2_4_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component14.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 39 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 40 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 53 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 54 = 0)
    (d2Equation2 : values 55 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 23 * d3Inverse0 - 1 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 26 * d3Inverse1 - 1 = 0)
    (d3Equation2 : values 28 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values2 ⟨index.val, inside⟩
    else d2Inverse0
  let values4 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d3Inverse0
    else d3Inverse1
  apply Krenn.Component14.SelectedLeafB6_2_4_6.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB6_2_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB6_2_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB6_2_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB6_2_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB6_2_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB6_2_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨351, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB6_2_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨460, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB6_2_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨524, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB6_2_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB6_2_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨633, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB6_2_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB6_2_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB6_2_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB6_2_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB6_2_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component14.SelectedBridgeB6_2_4_6.selectedLeafB6_2_4_6Impossible

end Krenn.Component14.SelectedBridgeB6_2_4_6
