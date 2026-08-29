import KrennComponent47.Root
import KrennComponent47.SelectedLeafB4_4

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component47.SelectedBridgeB4_4

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component47.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 40 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  let values1 : Fin 59 → R := fun index =>
    if inside : index.val < 58 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.Component47.SelectedLeafB4_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨208, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨247, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨250, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨287, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨366, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨376, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨377, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨528, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨586, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component47.Root.rootEquations, Krenn.Component47.SelectedLeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component47.SelectedBridgeB4_4.selectedLeafB4_4Impossible

end Krenn.Component47.SelectedBridgeB4_4
