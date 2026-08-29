import KrennComponent36.Root
import KrennComponent36.SelectedLeafB0_3_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component36.SelectedBridgeB0_3_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_3_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component36.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 41 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := values
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component36.SelectedLeafB0_3_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨134, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨139, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨158, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨233, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨253, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨257, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨276, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨303, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨305, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨307, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨377, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨407, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨448, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨451, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨453, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨552, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨594, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨613, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨651, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨662, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component36.SelectedBridgeB0_3_1.selectedLeafB0_3_1Impossible

end Krenn.Component36.SelectedBridgeB0_3_1
