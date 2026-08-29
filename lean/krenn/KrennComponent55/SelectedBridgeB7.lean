import KrennComponent55.Root
import KrennComponent55.SelectedLeafB7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component55.SelectedBridgeB7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component55.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 58 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 58 then
      d0Inverse0
    else if at1 : index.val = 59 then
      d0Inverse1
    else d0Inverse2
  apply Krenn.Component55.SelectedLeafB7.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨40, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨226, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨228, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨233, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨238, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨268, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨338, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨343, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨345, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨367, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨368, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨387, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨388, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨543, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨545, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨554, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨578, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component55.SelectedBridgeB7.selectedLeafB7Impossible

end Krenn.Component55.SelectedBridgeB7
