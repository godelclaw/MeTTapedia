import KrennComponent13.Root
import KrennComponent13.SelectedLeafB6_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component13.SelectedBridgeB6_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component13.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 37 = 0)
    (d1Equation1 : values 38 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 39 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 58 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 58 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.Component13.SelectedLeafB6_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨150, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨152, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨155, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨188, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨251, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨284, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨325, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨371, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨372, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨376, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨381, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨432, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨483, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨525, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨544, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨545, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨550, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component13.SelectedBridgeB6_1.selectedLeafB6_1Impossible

end Krenn.Component13.SelectedBridgeB6_1
