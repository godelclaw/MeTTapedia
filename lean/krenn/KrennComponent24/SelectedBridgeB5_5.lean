import KrennComponent24.Root
import KrennComponent24.SelectedLeafB5_5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component24.SelectedBridgeB5_5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component24.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 41 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 42 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 43 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.Component24.SelectedLeafB5_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨128, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨153, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨154, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨158, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨159, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨259, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨299, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨307, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨308, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨321, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨323, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨328, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨330, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨417, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨430, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨441, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨442, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨451, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨452, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨457, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨461, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨470, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨472, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨482, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨486, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨503, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨504, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨516, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨547, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨588, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨614, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨647, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨652, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨656, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨663, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component24.SelectedBridgeB5_5.selectedLeafB5_5Impossible

end Krenn.Component24.SelectedBridgeB5_5
