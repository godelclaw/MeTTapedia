import KrennComponent14.Root
import KrennComponent14.SelectedLeafB4_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component14.SelectedBridgeB4_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component14.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 38 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 39 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 40 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 60 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d1Inverse0
    else if at1 : index.val = 61 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component14.SelectedLeafB4_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨132, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨133, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨195, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨282, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨309, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨342, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨343, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨351, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨383, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨384, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨460, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨465, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨470, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨476, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨524, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨633, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component14.SelectedBridgeB4_7.selectedLeafB4_7Impossible

end Krenn.Component14.SelectedBridgeB4_7
