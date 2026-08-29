import KrennComponent37.Root
import KrennComponent37.SelectedLeafB0_2_2_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component37.SelectedBridgeB0_2_2_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_2_2_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component37.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    (d3Equation0 : values 25 = 0)
    (d3Equation1 : values 27 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 30 * d3Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := values
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  let values4 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values3 ⟨index.val, inside⟩
    else d3Inverse2
  apply Krenn.Component37.SelectedLeafB0_2_2_1.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨181, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨295, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨315, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨317, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨411, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨424, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨446, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨566, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0

#print axioms Krenn.Component37.SelectedBridgeB0_2_2_1.selectedLeafB0_2_2_1Impossible

end Krenn.Component37.SelectedBridgeB0_2_2_1
