import KrennComponent53.Root
import KrennComponent53.SelectedLeafB4_5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component53.SelectedBridgeB4_5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component53.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 41 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 42 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 43 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.Component53.SelectedLeafB4_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨230, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨244, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨333, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨386, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨477, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨636, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component53.Root.rootEquations, Krenn.Component53.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component53.SelectedBridgeB4_5.selectedLeafB4_5Impossible

end Krenn.Component53.SelectedBridgeB4_5
