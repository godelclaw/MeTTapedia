import KrennComponent37.Root
import KrennComponent37.SelectedLeafB5_2_5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component37.SelectedBridgeB5_2_5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_2_5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component37.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 56 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse0
    else d2Inverse2
  apply Krenn.Component37.SelectedLeafB5_2_5.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨147, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨149, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨152, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨221, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨283, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨298, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨313, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨403, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨427, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨484, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨591, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨645, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨648, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨656, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB5_2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component37.SelectedBridgeB5_2_5.selectedLeafB5_2_5Impossible

end Krenn.Component37.SelectedBridgeB5_2_5
