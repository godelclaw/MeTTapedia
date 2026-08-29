import KrennComponent45.Root
import KrennComponent45.SelectedLeafB4_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component45.SelectedBridgeB4_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component45.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 58 → R := fun index =>
    if inside : index.val < 57 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 60 → R := fun index =>
    if inside : index.val < 58 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 58 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.Component45.SelectedLeafB4_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨267, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨284, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨379, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨380, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨385, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨388, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨491, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨559, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component45.SelectedBridgeB4_6.selectedLeafB4_6Impossible

end Krenn.Component45.SelectedBridgeB4_6
