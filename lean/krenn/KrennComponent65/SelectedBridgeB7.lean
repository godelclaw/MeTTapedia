import KrennComponent65.Root
import KrennComponent65.SelectedLeafB7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component65.SelectedBridgeB7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component65.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else if at1 : index.val = 62 then
      d0Inverse1
    else d0Inverse2
  apply Krenn.Component65.SelectedLeafB7.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨199, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨201, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨202, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨212, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨260, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨275, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨303, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨304, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨320, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨423, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨424, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨447, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨477, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨540, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨541, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨543, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨558, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨588, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨589, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨613, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨615, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨645, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨647, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨659, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component65.Root.rootEquations, Krenn.Component65.SelectedLeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component65.SelectedBridgeB7.selectedLeafB7Impossible

end Krenn.Component65.SelectedBridgeB7
