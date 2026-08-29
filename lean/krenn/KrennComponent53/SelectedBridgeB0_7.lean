import KrennComponent53.Root
import KrennComponent53.SelectedLeafB0_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component53.SelectedBridgeB0_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component53.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 41 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 43 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 61 → R := values
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d1Inverse0
    else if at1 : index.val = 62 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component53.SelectedLeafB0_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨208, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component53.SelectedBridgeB0_7.selectedLeafB0_7Impossible

end Krenn.Component53.SelectedBridgeB0_7
