import KrennComponent36.Root
import KrennComponent36.SelectedLeafB0_6_5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component36.SelectedBridgeB0_6_5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_6_5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component36.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := values
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
      d2Inverse0
    else d2Inverse2
  apply Krenn.Component36.SelectedLeafB0_6_5.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨320, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component36.SelectedBridgeB0_6_5.selectedLeafB0_6_5Impossible

end Krenn.Component36.SelectedBridgeB0_6_5
