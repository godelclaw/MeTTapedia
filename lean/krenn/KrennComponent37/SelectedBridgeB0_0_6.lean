import KrennComponent37.Root
import KrennComponent37.SelectedLeafB0_0_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component37.SelectedBridgeB0_0_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_0_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component37.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 62 → R := values
  let values2 : Fin 62 → R := values1
  let values3 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d2Inverse0
    else d2Inverse1
  apply Krenn.Component37.SelectedLeafB0_0_6.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨175, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨176, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨180, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨181, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨279, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨295, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨296, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨307, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨310, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨317, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨393, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨407, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨411, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨427, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨429, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨433, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨446, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨465, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨479, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨500, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨566, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨628, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component37.SelectedBridgeB0_0_6.selectedLeafB0_0_6Impossible

end Krenn.Component37.SelectedBridgeB0_0_6
