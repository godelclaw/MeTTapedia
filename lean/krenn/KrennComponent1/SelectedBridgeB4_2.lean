import KrennComponent1.Root
import KrennComponent1.SelectedLeafB4_2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component1.SelectedBridgeB4_2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 58 → R := fun index =>
    if inside : index.val < 57 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 59 → R := fun index =>
    if inside : index.val < 58 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.Component1.SelectedLeafB4_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨57, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨220, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨230, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨252, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨259, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨260, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨265, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨276, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨354, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨364, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨366, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨369, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨370, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨384, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨385, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨448, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨503, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨527, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨534, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨537, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨545, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨551, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨563, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨571, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component1.SelectedBridgeB4_2.selectedLeafB4_2Impossible

end Krenn.Component1.SelectedBridgeB4_2
