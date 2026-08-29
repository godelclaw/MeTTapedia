import KrennComponent13.Root
import KrennComponent13.SelectedLeafB4_2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component13.SelectedBridgeB4_2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component13.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 37 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 38 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 39 = 0)
    : False := by
  let values1 : Fin 59 → R := fun index =>
    if inside : index.val < 58 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.Component13.SelectedLeafB4_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨133, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨152, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨153, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨177, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨183, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨188, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨234, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨264, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨325, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨368, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨373, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨376, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨377, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨382, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨431, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨444, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨483, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨484, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨485, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨489, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨525, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨544, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨545, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨564, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨573, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component13.SelectedBridgeB4_2.selectedLeafB4_2Impossible

end Krenn.Component13.SelectedBridgeB4_2
