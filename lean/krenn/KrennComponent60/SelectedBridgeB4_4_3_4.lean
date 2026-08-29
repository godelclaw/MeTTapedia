import KrennComponent60.Root
import KrennComponent60.SelectedLeafB4_4_3_4

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component60.SelectedBridgeB4_4_3_4

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_4_3_4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 40 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 25 * d3Inverse0 - 1 = 0)
    (d3Equation1 : values 28 = 0)
    (d3Equation2 : values 29 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d2Inverse1
    else d2Inverse2
  let values4 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values3 ⟨index.val, inside⟩
    else d3Inverse0
  apply Krenn.Component60.SelectedLeafB4_4_3_4.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨70, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨99, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨148, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨150, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨154, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨155, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨213, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨298, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨304, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨372, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨377, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨436, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨497, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨500, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨537, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨605, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨654, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_4_3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component60.SelectedBridgeB4_4_3_4.selectedLeafB4_4_3_4Impossible

end Krenn.Component60.SelectedBridgeB4_4_3_4
