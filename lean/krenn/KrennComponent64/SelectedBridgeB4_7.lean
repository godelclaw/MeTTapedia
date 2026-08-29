import KrennComponent64.Root
import KrennComponent64.SelectedLeafB4_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component64.SelectedBridgeB4_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component64.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 37 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 38 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 39 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d1Inverse0
    else if at1 : index.val = 62 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component64.SelectedLeafB4_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨231, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨235, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨243, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨351, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨367, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨372, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨388, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨415, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨416, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨418, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨548, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨570, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨576, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨632, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨634, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component64.SelectedBridgeB4_7.selectedLeafB4_7Impossible

end Krenn.Component64.SelectedBridgeB4_7
