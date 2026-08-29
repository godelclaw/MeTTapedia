import KrennComponent11.Root
import KrennComponent11.SelectedLeafB6_6_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component11.SelectedBridgeB6_6_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_6_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component11.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Equation1 : values 56 = 0)
    (d2Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 65 → R := values2
  apply Krenn.Component11.SelectedLeafB6_6_0.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨175, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨262, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨268, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨329, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨330, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨341, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨342, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨453, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨662, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component11.Root.rootEquations, Krenn.Component11.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component11.SelectedBridgeB6_6_0.selectedLeafB6_6_0Impossible

end Krenn.Component11.SelectedBridgeB6_6_0
