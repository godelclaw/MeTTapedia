import KrennComponent13.Root
import KrennComponent13.SelectedLeafB6_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component13.SelectedBridgeB6_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component13.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 37 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 38 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 39 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 58 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 58 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component13.SelectedLeafB6_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨150, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨152, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨154, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨155, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨156, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨157, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨177, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨183, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨188, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨202, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨217, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨223, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨234, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨240, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨241, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨284, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨365, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨372, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨377, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨381, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨407, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨408, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨409, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨417, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨419, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨431, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨432, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨483, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨484, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨485, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨498, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨532, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨545, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨552, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨564, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨575, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨594, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component13.SelectedBridgeB6_3.selectedLeafB6_3Impossible

end Krenn.Component13.SelectedBridgeB6_3
