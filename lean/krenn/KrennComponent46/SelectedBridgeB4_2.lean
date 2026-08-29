import KrennComponent46.Root
import KrennComponent46.SelectedLeafB4_2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component46.SelectedBridgeB4_2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component46.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 41 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 43 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.Component46.SelectedLeafB4_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨174, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨186, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨197, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨201, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨202, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨204, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨206, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨229, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨351, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨357, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨395, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨398, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨494, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨562, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨586, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨633, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨638, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component46.Root.rootEquations, Krenn.Component46.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component46.SelectedBridgeB4_2.selectedLeafB4_2Impossible

end Krenn.Component46.SelectedBridgeB4_2
