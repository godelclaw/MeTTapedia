import KrennComponent10.Root
import KrennComponent10.SelectedLeafB4_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component10.SelectedBridgeB4_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 41 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component10.SelectedLeafB4_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨177, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨186, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨369, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨373, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨375, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨398, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨409, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨446, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨513, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨550, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨628, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨633, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨634, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component10.SelectedBridgeB4_3.selectedLeafB4_3Impossible

end Krenn.Component10.SelectedBridgeB4_3
