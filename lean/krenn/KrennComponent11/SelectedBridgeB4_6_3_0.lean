import KrennComponent11.Root
import KrennComponent11.SelectedLeafB4_6_3_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component11.SelectedBridgeB4_6_3_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_6_3_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component11.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    (d3Equation0 : values 24 = 0)
    (d3Equation1 : values 27 = 0)
    (d3Equation2 : values 30 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d2Inverse1
    else d2Inverse2
  let values4 : Fin 66 → R := values3
  apply Krenn.Component11.SelectedLeafB4_6_3_0.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨183, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨262, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨286, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨322, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨328, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨329, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨340, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨341, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨453, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨489, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨588, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨614, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨662, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB4_6_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component11.SelectedBridgeB4_6_3_0.selectedLeafB4_6_3_0Impossible

end Krenn.Component11.SelectedBridgeB4_6_3_0
