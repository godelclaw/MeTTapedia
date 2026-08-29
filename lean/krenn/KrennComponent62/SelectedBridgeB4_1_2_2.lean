import KrennComponent62.Root
import KrennComponent62.SelectedLeafB4_1_2_2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component62.SelectedBridgeB4_1_2_2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_1_2_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component62.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 37 = 0)
    (d1Equation1 : values 38 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 39 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 54 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 55 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 56 = 0)
    (d3Equation0 : values 23 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 26 * d3Inverse1 - 1 = 0)
    (d3Equation2 : values 27 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  let values4 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values3 ⟨index.val, inside⟩
    else d3Inverse1
  apply Krenn.Component62.SelectedLeafB4_1_2_2.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨147, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨153, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨226, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨408, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨414, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨439, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨442, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨444, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨526, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨549, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨558, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨559, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨600, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨631, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨649, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component62.Root.rootEquations, Krenn.Component62.SelectedLeafB4_1_2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component62.SelectedBridgeB4_1_2_2.selectedLeafB4_1_2_2Impossible

end Krenn.Component62.SelectedBridgeB4_1_2_2
