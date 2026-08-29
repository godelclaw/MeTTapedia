import KrennComponent24.Root
import KrennComponent24.SelectedLeafB5_7_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component24.SelectedBridgeB5_7_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_7_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component24.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 41 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 43 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Equation2 : values 58 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 67 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else if at1 : index.val = 65 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 67 → R := values2
  apply Krenn.Component24.SelectedLeafB5_7_0.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨130, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨131, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨135, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨149, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨151, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨153, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨232, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨259, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨266, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨305, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨306, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨323, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨406, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨417, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨447, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨457, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨472, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨549, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨550, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨564, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨590, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨611, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨614, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨652, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨656, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨662, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨663, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB5_7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component24.SelectedBridgeB5_7_0.selectedLeafB5_7_0Impossible

end Krenn.Component24.SelectedBridgeB5_7_0
