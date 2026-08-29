import KrennComponent58.Root
import KrennComponent58.SelectedLeafB6_6_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component58.SelectedBridgeB6_6_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_6_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component58.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 38 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 39 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 40 = 0)
    (d2Equation0 : values 53 = 0)
    (d2Equation1 : values 54 = 0)
    (d2Equation2 : values 55 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 63 → R := values2
  apply Krenn.Component58.SelectedLeafB6_6_0.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨224, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨225, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨241, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨339, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨340, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨342, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨474, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨562, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component58.SelectedBridgeB6_6_0.selectedLeafB6_6_0Impossible

end Krenn.Component58.SelectedBridgeB6_6_0
