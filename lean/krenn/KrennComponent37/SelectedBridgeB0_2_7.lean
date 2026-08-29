import KrennComponent37.Root
import KrennComponent37.SelectedLeafB0_2_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component37.SelectedBridgeB0_2_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_2_7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component37.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := values
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 63 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d2Inverse0
    else if at1 : index.val = 64 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component37.SelectedLeafB0_2_7.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨175, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨176, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨178, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨180, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨183, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨255, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨256, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨257, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨260, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨266, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨279, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨283, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨295, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨296, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨298, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨299, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨307, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨308, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨310, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨317, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨369, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨393, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨407, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨408, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨411, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨414, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨424, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨426, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨427, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨429, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨445, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨446, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨449, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨453, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨465, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨472, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨474, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨479, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨482, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨498, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨502, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨519, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨541, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨562, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨566, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨605, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨623, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨624, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨626, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨628, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨642, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨645, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨656, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component37.SelectedBridgeB0_2_7.selectedLeafB0_2_7Impossible

end Krenn.Component37.SelectedBridgeB0_2_7
