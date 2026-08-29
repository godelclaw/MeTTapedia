import KrennComponent24.Root
import KrennComponent24.SelectedLeafB2_2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component24.SelectedBridgeB2_2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB2_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component24.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 41 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 43 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.Component24.SelectedLeafB2_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨282, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨304, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨307, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨323, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨457, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨663, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component24.SelectedBridgeB2_2.selectedLeafB2_2Impossible

end Krenn.Component24.SelectedBridgeB2_2
