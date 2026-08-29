import KrennComponent64.Root
import KrennComponent64.SelectedLeafB4_2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component64.SelectedBridgeB4_2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component64.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 37 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 38 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 39 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.Component64.SelectedLeafB4_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨71, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨205, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨209, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨231, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨235, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨243, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨283, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨284, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨309, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨310, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨343, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨351, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨358, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨367, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨369, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨390, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨415, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨433, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨444, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨479, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨548, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨576, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨577, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨632, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨634, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component64.SelectedBridgeB4_2.selectedLeafB4_2Impossible

end Krenn.Component64.SelectedBridgeB4_2
