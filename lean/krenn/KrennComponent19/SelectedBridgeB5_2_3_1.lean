import KrennComponent19.Root
import KrennComponent19.SelectedLeafB5_2_3_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component19.SelectedBridgeB5_2_3_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_2_3_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component19.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 42 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 43 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 44 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    (d3Equation0 : values 26 = 0)
    (d3Equation1 : values 29 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 32 * d3Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse1
    else d2Inverse2
  let values4 : Fin 68 → R := fun index =>
    if inside : index.val < 67 then
      values3 ⟨index.val, inside⟩
    else d3Inverse2
  apply Krenn.Component19.SelectedLeafB5_2_3_1.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨220, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨267, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨304, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨319, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨324, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨403, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨420, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨424, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨429, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨442, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨446, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨470, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨565, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨662, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component19.SelectedBridgeB5_2_3_1.selectedLeafB5_2_3_1Impossible

end Krenn.Component19.SelectedBridgeB5_2_3_1
