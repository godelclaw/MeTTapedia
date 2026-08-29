import KrennComponent18.Root
import KrennComponent18.SelectedLeafB4_2_3_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component18.SelectedBridgeB4_2_3_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_2_3_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component18.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 41 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 43 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    (d3Equation0 : values 25 = 0)
    (d3Equation1 : values 28 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 31 * d3Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d2Inverse1
    else d2Inverse2
  let values4 : Fin 66 → R := fun index =>
    if inside : index.val < 65 then
      values3 ⟨index.val, inside⟩
    else d3Inverse2
  apply Krenn.Component18.SelectedLeafB4_2_3_1.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨99, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨144, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨148, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨149, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨181, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨183, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨213, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨266, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨304, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨311, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨313, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨319, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨323, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨328, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨332, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨379, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨387, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨398, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨424, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨428, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨459, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨474, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨495, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨501, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨505, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨508, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨551, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨564, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨624, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨638, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨648, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨651, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨653, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨656, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB4_2_3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component18.SelectedBridgeB4_2_3_1.selectedLeafB4_2_3_1Impossible

end Krenn.Component18.SelectedBridgeB4_2_3_1
