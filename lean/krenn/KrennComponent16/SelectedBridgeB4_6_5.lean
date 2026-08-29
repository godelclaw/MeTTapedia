import KrennComponent16.Root
import KrennComponent16.SelectedLeafB4_6_5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component16.SelectedBridgeB4_6_5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_6_5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component16.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 41 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 43 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse0
    else d2Inverse2
  apply Krenn.Component16.SelectedLeafB4_6_5.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨68, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨247, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨273, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨314, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨436, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨441, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨447, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨448, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨497, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨518, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨540, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨660, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB4_6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component16.SelectedBridgeB4_6_5.selectedLeafB4_6_5Impossible

end Krenn.Component16.SelectedBridgeB4_6_5
