import KrennComponent24.Root
import KrennComponent24.SelectedLeafB6_2_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component24.SelectedBridgeB6_2_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_2_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component24.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 41 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 43 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Equation1 : values 57 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component24.SelectedLeafB6_2_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨130, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨177, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨306, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨319, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨326, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨337, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨479, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨525, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨589, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨591, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨593, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨616, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨618, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨653, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component24.Root.rootEquations, Krenn.Component24.SelectedLeafB6_2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component24.SelectedBridgeB6_2_1.selectedLeafB6_2_1Impossible

end Krenn.Component24.SelectedBridgeB6_2_1
