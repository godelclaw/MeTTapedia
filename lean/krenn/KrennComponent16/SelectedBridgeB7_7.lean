import KrennComponent16.Root
import KrennComponent16.SelectedLeafB7_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component16.SelectedBridgeB7_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB7_7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component16.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 41 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 43 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 65 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else if at1 : index.val = 63 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 68 → R := fun index =>
    if inside : index.val < 65 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d1Inverse0
    else if at1 : index.val = 66 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component16.SelectedLeafB7_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨142, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨250, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨298, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨303, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨314, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨319, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨326, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨328, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨392, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨407, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨408, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨431, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨442, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨448, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨503, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨567, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨571, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨588, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨652, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨654, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨659, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component16.SelectedBridgeB7_7.selectedLeafB7_7Impossible

end Krenn.Component16.SelectedBridgeB7_7
