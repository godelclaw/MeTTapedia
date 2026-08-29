import KrennComponent25.Root
import KrennComponent25.SelectedLeafB7_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component25.SelectedBridgeB7_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB7_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component25.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 41 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else if at1 : index.val = 62 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component25.SelectedLeafB7_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨142, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨144, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨145, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨146, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨147, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨148, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨149, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨150, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨151, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨157, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨175, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨188, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨195, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨238, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨257, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨292, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨306, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨326, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨402, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨406, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨433, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨439, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨449, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨552, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨579, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨586, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨588, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨605, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨643, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨647, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨654, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component25.SelectedBridgeB7_3.selectedLeafB7_3Impossible

end Krenn.Component25.SelectedBridgeB7_3
