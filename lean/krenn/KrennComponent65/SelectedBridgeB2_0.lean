import KrennComponent65.Root
import KrennComponent65.SelectedLeafB2_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component65.SelectedBridgeB2_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB2_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component65.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Equation1 : values 39 = 0)
    (d1Equation2 : values 40 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 62 → R := values1
  apply Krenn.Component65.SelectedLeafB2_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨175, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨176, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨178, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨186, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨241, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨254, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨278, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨309, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨310, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨315, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨376, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨378, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨411, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨416, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨420, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨421, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨423, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨528, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨540, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component65.SelectedBridgeB2_0.selectedLeafB2_0Impossible

end Krenn.Component65.SelectedBridgeB2_0
