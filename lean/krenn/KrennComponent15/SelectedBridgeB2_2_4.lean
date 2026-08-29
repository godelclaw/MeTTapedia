import KrennComponent15.Root
import KrennComponent15.SelectedLeafB2_2_4

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component15.SelectedBridgeB2_2_4

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB2_2_4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component15.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 36 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 37 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 38 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 51 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 52 = 0)
    (d2Equation2 : values 53 = 0)
    : False := by
  let values1 : Fin 58 → R := fun index =>
    if inside : index.val < 57 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 59 → R := fun index =>
    if inside : index.val < 58 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values2 ⟨index.val, inside⟩
    else d2Inverse0
  apply Krenn.Component15.SelectedLeafB2_2_4.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB2_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB2_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB2_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB2_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨229, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB2_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨315, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB2_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨367, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB2_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨368, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB2_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB2_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB2_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB2_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB2_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB2_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB2_2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component15.SelectedBridgeB2_2_4.selectedLeafB2_2_4Impossible

end Krenn.Component15.SelectedBridgeB2_2_4
