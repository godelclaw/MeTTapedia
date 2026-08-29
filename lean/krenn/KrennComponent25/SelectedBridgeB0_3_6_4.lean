import KrennComponent25.Root
import KrennComponent25.SelectedLeafB0_3_6_4

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component25.SelectedBridgeB0_3_6_4

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_3_6_4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component25.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 41 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 55 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 57 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 24 * d3Inverse0 - 1 = 0)
    (d3Equation1 : values 26 = 0)
    (d3Equation2 : values 29 = 0)
    : False := by
  let values1 : Fin 61 → R := values
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d2Inverse0
    else d2Inverse1
  let values4 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values3 ⟨index.val, inside⟩
    else d3Inverse0
  apply Krenn.Component25.SelectedLeafB0_3_6_4.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨149, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨151, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨153, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨177, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨195, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨257, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨319, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨435, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨461, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨605, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨643, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨654, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component25.SelectedBridgeB0_3_6_4.selectedLeafB0_3_6_4Impossible

end Krenn.Component25.SelectedBridgeB0_3_6_4
