import KrennComponent39.Root
import KrennComponent39.SelectedLeafB6_2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component39.SelectedBridgeB6_2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component39.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 39 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 40 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.Component39.SelectedLeafB6_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨313, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨314, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨317, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨325, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨375, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨382, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨430, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨431, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨446, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨451, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨452, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨476, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨505, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨508, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨534, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨566, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨591, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨600, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨626, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨646, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨651, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨658, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨660, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component39.SelectedBridgeB6_2.selectedLeafB6_2Impossible

end Krenn.Component39.SelectedBridgeB6_2
