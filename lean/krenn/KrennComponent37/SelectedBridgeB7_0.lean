import KrennComponent37.Root
import KrennComponent37.SelectedLeafB7_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component37.SelectedBridgeB7_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB7_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component37.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 65 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else if at1 : index.val = 63 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 65 → R := values1
  apply Krenn.Component37.SelectedLeafB7_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨149, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨152, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨181, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨221, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨296, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨297, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨308, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨393, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨424, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨427, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨446, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨447, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨474, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨476, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨541, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨555, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨566, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨628, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨629, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨646, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component37.SelectedBridgeB7_0.selectedLeafB7_0Impossible

end Krenn.Component37.SelectedBridgeB7_0
