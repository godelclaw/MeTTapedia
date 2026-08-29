import KrennComponent37.Root
import KrennComponent37.SelectedLeafB5_2_6_5_2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component37.SelectedBridgeB5_2_6_5_2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_2_6_5_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component37.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 25 * d3Inverse0 - 1 = 0)
    (d3Equation1 : values 27 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 30 * d3Inverse2 - 1 = 0)
    (d4Equation0 : values 59 = 0)
    (d4Inverse1 : R)
    (d4Equation1 : values 60 * d4Inverse1 - 1 = 0)
    (d4Equation2 : values 61 = 0)
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
      d2Inverse0
    else d2Inverse1
  let values4 : Fin 69 → R := fun index =>
    if inside : index.val < 67 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 67 then
      d3Inverse0
    else d3Inverse2
  let values5 : Fin 70 → R := fun index =>
    if inside : index.val < 69 then
      values4 ⟨index.val, inside⟩
    else d4Inverse1
  apply Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedHasNoCommonZero values5
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨147, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨151, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨154, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨156, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨157, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨175, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨224, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨298, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨299, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨303, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨308, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨338, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨354, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨369, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨399, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨401, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨403, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨406, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨410, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨428, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨430, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨435, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨437, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨439, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨449, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨453, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨461, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨470, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨484, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨505, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨510, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨523, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨525, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨594, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨605, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨620, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨645, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨648, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨656, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_6_5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d4Equation0

#print axioms Krenn.Component37.SelectedBridgeB5_2_6_5_2.selectedLeafB5_2_6_5_2Impossible

end Krenn.Component37.SelectedBridgeB5_2_6_5_2
