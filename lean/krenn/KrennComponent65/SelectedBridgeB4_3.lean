import KrennComponent65.Root
import KrennComponent65.SelectedLeafB4_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component65.SelectedBridgeB4_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component65.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 39 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 40 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component65.SelectedLeafB4_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨254, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨304, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨309, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨310, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨320, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨412, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨414, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨420, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨421, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨423, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨447, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨540, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component65.SelectedBridgeB4_3.selectedLeafB4_3Impossible

end Krenn.Component65.SelectedBridgeB4_3
