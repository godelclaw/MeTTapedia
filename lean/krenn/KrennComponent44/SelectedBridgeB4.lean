import KrennComponent44.Root
import KrennComponent44.SelectedLeafB4

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component44.SelectedBridgeB4

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component44.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  apply Krenn.Component44.SelectedLeafB4.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨40, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨151, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨152, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨153, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨156, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨157, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨159, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨181, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨197, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨199, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨200, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨201, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨202, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨224, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨226, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨228, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨238, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨242, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨243, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨254, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨309, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨333, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨355, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨367, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨369, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨395, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨397, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨415, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨421, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨422, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨428, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨446, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨484, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨485, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨500, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨509, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨535, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨536, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨551, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨552, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨553, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, Krenn.Component44.Root.rootEquations, Krenn.Component44.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component44.SelectedBridgeB4.selectedLeafB4Impossible

end Krenn.Component44.SelectedBridgeB4
