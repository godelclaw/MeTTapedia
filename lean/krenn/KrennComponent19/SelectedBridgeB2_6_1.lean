import KrennComponent19.Root
import KrennComponent19.SelectedLeafB2_6_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component19.SelectedBridgeB2_6_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB2_6_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component19.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 42 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 43 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 44 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component19.SelectedLeafB2_6_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB2_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨324, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB2_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨413, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB2_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨452, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB2_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB2_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB2_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB2_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB2_6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component19.SelectedBridgeB2_6_1.selectedLeafB2_6_1Impossible

end Krenn.Component19.SelectedBridgeB2_6_1
