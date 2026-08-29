import KrennComponent15.Root
import KrennComponent15.SelectedLeafB6_6_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component15.SelectedBridgeB6_6_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_6_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component15.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 36 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 37 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 38 = 0)
    (d2Equation0 : values 51 = 0)
    (d2Equation1 : values 52 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 53 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 59 → R := fun index =>
    if inside : index.val < 57 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 57 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 61 → R := fun index =>
    if inside : index.val < 59 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component15.SelectedLeafB6_6_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB6_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component15.SelectedBridgeB6_6_1.selectedLeafB6_6_1Impossible

end Krenn.Component15.SelectedBridgeB6_6_1
