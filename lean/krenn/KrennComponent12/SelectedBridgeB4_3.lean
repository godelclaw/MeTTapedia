import KrennComponent12.Root
import KrennComponent12.SelectedLeafB4_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component12.SelectedBridgeB4_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component12.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 39 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 40 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component12.SelectedLeafB4_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨201, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨216, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨218, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨296, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨333, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨334, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨338, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨339, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨351, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨436, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨444, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨473, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨490, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨498, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨513, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨516, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨561, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨562, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨576, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨577, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component12.SelectedBridgeB4_3.selectedLeafB4_3Impossible

end Krenn.Component12.SelectedBridgeB4_3
