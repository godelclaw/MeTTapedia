import KrennComponent36.Root
import KrennComponent36.SelectedLeafB4_0_4

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component36.SelectedBridgeB4_0_4

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_0_4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component36.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Equation1 : values 40 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 63 → R := values1
  let values3 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values2 ⟨index.val, inside⟩
    else d2Inverse0
  apply Krenn.Component36.SelectedLeafB4_0_4.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨253, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨272, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨305, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨307, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨448, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨451, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨662, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB4_0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component36.SelectedBridgeB4_0_4.selectedLeafB4_0_4Impossible

end Krenn.Component36.SelectedBridgeB4_0_4
