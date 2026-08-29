import KrennComponent13.Root
import KrennComponent13.SelectedLeafB4_4_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component13.SelectedBridgeB4_4_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_4_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component13.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 37 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 38 = 0)
    (d1Equation2 : values 39 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 52 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 53 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 54 = 0)
    : False := by
  let values1 : Fin 59 → R := fun index =>
    if inside : index.val < 58 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  let values3 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d2Inverse0
    else d2Inverse1
  apply Krenn.Component13.SelectedLeafB4_4_6.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨188, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨284, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨325, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨376, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨483, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨525, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component13.SelectedBridgeB4_4_6.selectedLeafB4_4_6Impossible

end Krenn.Component13.SelectedBridgeB4_4_6
