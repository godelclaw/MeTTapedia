import KrennComponent39.Root
import KrennComponent39.SelectedLeafB3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component39.SelectedBridgeB3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component39.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse1
    else d0Inverse2
  apply Krenn.Component39.SelectedLeafB3.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨326, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨430, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨566, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨660, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1

#print axioms Krenn.Component39.SelectedBridgeB3.selectedLeafB3Impossible

end Krenn.Component39.SelectedBridgeB3
