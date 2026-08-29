import KrennComponent20.Root
import KrennComponent20.SelectedLeafB4_2_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component20.SelectedBridgeB4_2_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_2_7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component20.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 54 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 55 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 56 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 62 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d2Inverse0
    else if at1 : index.val = 63 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component20.SelectedLeafB4_2_7.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨107, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨133, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨144, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨146, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨165, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨183, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨185, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨186, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨199, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨284, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨285, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨288, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨345, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨388, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨415, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨470, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨473, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨485, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨490, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨506, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨511, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨551, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨558, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨635, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1

#print axioms Krenn.Component20.SelectedBridgeB4_2_7.selectedLeafB4_2_7Impossible

end Krenn.Component20.SelectedBridgeB4_2_7
