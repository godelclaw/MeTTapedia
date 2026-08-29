import KrennComponent1.Root
import KrennComponent1.SelectedLeafB5_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component1.SelectedBridgeB5_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
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
    : False := by
  let values1 : Fin 59 → R := fun index =>
    if inside : index.val < 57 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 57 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 61 → R := fun index =>
    if inside : index.val < 59 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component1.SelectedLeafB5_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨40, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨47, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨218, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨219, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨220, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨224, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨225, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨229, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨260, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨264, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨265, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨276, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨292, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨354, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨371, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨382, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨384, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨385, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨386, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨392, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨448, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨503, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨521, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨545, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨546, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨548, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨550, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨559, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨560, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨564, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨579, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component1.SelectedBridgeB5_3.selectedLeafB5_3Impossible

end Krenn.Component1.SelectedBridgeB5_3
