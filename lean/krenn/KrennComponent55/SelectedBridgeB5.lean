import KrennComponent55.Root
import KrennComponent55.SelectedLeafB5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component55.SelectedBridgeB5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component55.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 58 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 58 then
      d0Inverse0
    else d0Inverse2
  apply Krenn.Component55.SelectedLeafB5.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨40, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨42, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨84, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨195, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨200, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨209, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨228, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨238, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨245, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨257, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨338, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨343, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨345, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨346, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨367, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨368, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨370, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨375, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨387, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨388, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨389, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨390, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨405, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨409, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨411, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨423, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨479, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨509, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨510, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨519, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨521, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨529, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨531, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨542, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨543, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨544, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨546, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨554, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨555, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨558, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨559, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨564, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨578, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, Krenn.Component55.Root.rootEquations, Krenn.Component55.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component55.SelectedBridgeB5.selectedLeafB5Impossible

end Krenn.Component55.SelectedBridgeB5
