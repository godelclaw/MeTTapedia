import KrennComponent15.Root
import KrennComponent15.SelectedLeafB6_2_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component15.SelectedBridgeB6_2_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_2_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component15.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 36 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 37 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 38 = 0)
    (d2Equation0 : values 51 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 52 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 53 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 59 → R := fun index =>
    if inside : index.val < 57 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 57 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component15.SelectedLeafB6_2_3.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨226, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨227, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨228, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨365, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨367, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨401, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨429, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨519, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨527, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨528, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1

#print axioms Krenn.Component15.SelectedBridgeB6_2_3.selectedLeafB6_2_3Impossible

end Krenn.Component15.SelectedBridgeB6_2_3
