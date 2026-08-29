import KrennComponent54.Root
import KrennComponent54.SelectedLeafB6_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component54.SelectedBridgeB6_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component54.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.Component54.SelectedLeafB6_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨89, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨182, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨200, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨205, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨224, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨230, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨241, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨288, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨351, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨364, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨366, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨409, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨510, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨526, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨561, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨565, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨586, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨629, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨638, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component54.SelectedBridgeB6_6.selectedLeafB6_6Impossible

end Krenn.Component54.SelectedBridgeB6_6
