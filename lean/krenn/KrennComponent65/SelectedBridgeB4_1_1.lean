import KrennComponent65.Root
import KrennComponent65.SelectedLeafB4_1_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component65.SelectedBridgeB4_1_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_1_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component65.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Equation1 : values 39 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 40 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Equation1 : values 56 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component65.SelectedLeafB4_1_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨254, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨278, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨309, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨310, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨315, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨317, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨412, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨414, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨420, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨421, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨423, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨424, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨435, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨447, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨482, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨499, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨504, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨540, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨589, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨615, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨647, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨648, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨659, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB4_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component65.SelectedBridgeB4_1_1.selectedLeafB4_1_1Impossible

end Krenn.Component65.SelectedBridgeB4_1_1
