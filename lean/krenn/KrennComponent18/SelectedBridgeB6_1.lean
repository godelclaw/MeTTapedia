import KrennComponent18.Root
import KrennComponent18.SelectedLeafB6_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component18.SelectedBridgeB6_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component18.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 41 = 0)
    (d1Equation1 : values 42 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 43 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.Component18.SelectedLeafB6_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨144, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨296, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨313, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨321, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨379, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨452, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨587, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨638, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨645, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨656, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component18.SelectedBridgeB6_1.selectedLeafB6_1Impossible

end Krenn.Component18.SelectedBridgeB6_1
