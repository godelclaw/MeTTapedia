import KrennComponent16.Root
import KrennComponent16.SelectedLeafB1_6_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component16.SelectedBridgeB1_6_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB1_6_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component16.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 41 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 43 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 65 → R := values2
  apply Krenn.Component16.SelectedLeafB1_6_0.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨407, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨433, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨501, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨527, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨649, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1

#print axioms Krenn.Component16.SelectedBridgeB1_6_0.selectedLeafB1_6_0Impossible

end Krenn.Component16.SelectedBridgeB1_6_0
