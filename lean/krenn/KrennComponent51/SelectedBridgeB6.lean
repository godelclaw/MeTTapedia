import KrennComponent51.Root
import KrennComponent51.SelectedLeafB6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component51.SelectedBridgeB6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component51.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d0Inverse0
    else d0Inverse1
  apply Krenn.Component51.SelectedLeafB6.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨100, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨175, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨176, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨177, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨185, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨195, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨200, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨201, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨205, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨206, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨240, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨263, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨340, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨368, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨370, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨372, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨373, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨374, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨375, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨376, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨377, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨378, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨380, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨382, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨383, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨384, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨385, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨390, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨392, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨433, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨444, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨448, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨470, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨488, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨500, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨509, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨512, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨513, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨538, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨568, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨574, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨591, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨594, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component51.SelectedBridgeB6.selectedLeafB6Impossible

end Krenn.Component51.SelectedBridgeB6
