import KrennComponent46.Root
import KrennComponent46.SelectedLeafB4_4

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component46.SelectedBridgeB4_4

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component46.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 41 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 42 = 0)
    (d1Equation2 : values 43 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.Component46.SelectedLeafB4_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨204, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨240, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨561, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component46.SelectedBridgeB4_4.selectedLeafB4_4Impossible

end Krenn.Component46.SelectedBridgeB4_4
