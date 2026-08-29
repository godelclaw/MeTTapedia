import KrennComponent24.Root
import KrennComponent24.SelectedLeafB6_1_4

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component24.SelectedBridgeB6_1_4

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_1_4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component24.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 41 = 0)
    (d1Equation1 : values 42 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 43 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else d2Inverse0
  apply Krenn.Component24.SelectedLeafB6_1_4.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨91, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨149, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨151, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨152, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨266, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨319, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨589, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0

#print axioms Krenn.Component24.SelectedBridgeB6_1_4.selectedLeafB6_1_4Impossible

end Krenn.Component24.SelectedBridgeB6_1_4
