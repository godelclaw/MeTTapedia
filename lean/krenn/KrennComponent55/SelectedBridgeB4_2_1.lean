import KrennComponent55.Root
import KrennComponent55.SelectedLeafB4_2_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component55.SelectedBridgeB4_2_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_2_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component55.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Equation0 : values 52 = 0)
    (d2Equation1 : values 53 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 54 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 59 → R := fun index =>
    if inside : index.val < 58 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component55.SelectedLeafB4_2_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨65, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨76, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨195, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨223, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨225, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨226, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨228, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨230, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨232, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨233, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨234, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨235, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨243, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨251, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨257, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨263, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨296, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨341, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨342, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨343, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨345, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨354, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨355, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨365, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨390, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨416, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨445, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨474, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨490, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨494, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨543, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨544, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨551, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨555, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨559, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB4_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component55.SelectedBridgeB4_2_1.selectedLeafB4_2_1Impossible

end Krenn.Component55.SelectedBridgeB4_2_1
