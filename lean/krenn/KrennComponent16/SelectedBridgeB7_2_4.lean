import KrennComponent16.Root
import KrennComponent16.SelectedLeafB7_2_4

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component16.SelectedBridgeB7_2_4

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB7_2_4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component16.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 41 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 43 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 65 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else if at1 : index.val = 63 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else d2Inverse0
  apply Krenn.Component16.SelectedLeafB7_2_4.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨142, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨247, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨448, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨588, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB7_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component16.SelectedBridgeB7_2_4.selectedLeafB7_2_4Impossible

end Krenn.Component16.SelectedBridgeB7_2_4
