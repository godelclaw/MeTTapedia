import KrennComponent54.Root
import KrennComponent54.SelectedLeafB4_2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component54.SelectedBridgeB4_2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component54.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.Component54.SelectedLeafB4_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨165, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨182, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨200, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨234, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨288, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨347, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨351, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨364, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨366, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨439, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨479, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨482, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨485, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨506, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨521, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨560, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨578, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨586, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨592, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨636, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨638, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component54.SelectedBridgeB4_2.selectedLeafB4_2Impossible

end Krenn.Component54.SelectedBridgeB4_2
