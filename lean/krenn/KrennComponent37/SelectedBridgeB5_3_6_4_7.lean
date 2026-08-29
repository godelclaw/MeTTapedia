import KrennComponent37.Root
import KrennComponent37.SelectedLeafB5_3_6_4_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component37.SelectedBridgeB5_3_6_4_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_3_6_4_7Impossible {R : Type*} [Field R] [CharZero R]
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
    (d1Inverse2 : R)
    (d1Equation2 : values 42 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 58 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 25 * d3Inverse0 - 1 = 0)
    (d3Equation1 : values 27 = 0)
    (d3Equation2 : values 30 = 0)
    (d4Inverse0 : R)
    (d4Equation0 : values 59 * d4Inverse0 - 1 = 0)
    (d4Inverse1 : R)
    (d4Equation1 : values 60 * d4Inverse1 - 1 = 0)
    (d4Inverse2 : R)
    (d4Equation2 : values 61 * d4Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 66 then
      d2Inverse0
    else d2Inverse1
  let values4 : Fin 69 → R := fun index =>
    if inside : index.val < 68 then
      values3 ⟨index.val, inside⟩
    else d3Inverse0
  let values5 : Fin 72 → R := fun index =>
    if inside : index.val < 69 then
      values4 ⟨index.val, inside⟩
    else if at0 : index.val = 69 then
      d4Inverse0
    else if at1 : index.val = 70 then
      d4Inverse1
    else d4Inverse2
  apply Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedHasNoCommonZero values5
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨148, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨175, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨181, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨216, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨279, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨296, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨298, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨299, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨334, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨370, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨476, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨542, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨566, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨605, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨656, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d4Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_3_6_4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d4Equation2

#print axioms Krenn.Component37.SelectedBridgeB5_3_6_4_7.selectedLeafB5_3_6_4_7Impossible

end Krenn.Component37.SelectedBridgeB5_3_6_4_7
