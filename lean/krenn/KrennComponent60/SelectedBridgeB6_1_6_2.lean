import KrennComponent60.Root
import KrennComponent60.SelectedLeafB6_1_6_2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component60.SelectedBridgeB6_1_6_2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_1_6_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Equation1 : values 40 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 41 * d1Inverse2 - 1 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 55 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 57 = 0)
    (d3Equation0 : values 25 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 28 * d3Inverse1 - 1 = 0)
    (d3Equation2 : values 29 = 0)
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
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d2Inverse0
    else d2Inverse1
  let values4 : Fin 67 → R := fun index =>
    if inside : index.val < 66 then
      values3 ⟨index.val, inside⟩
    else d3Inverse1
  apply Krenn.Component60.SelectedLeafB6_1_6_2.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨71, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨147, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨149, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨239, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨293, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨298, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨403, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨404, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨410, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨432, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨436, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨444, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨457, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨548, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨558, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨587, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨600, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨632, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨645, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨653, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component60.SelectedBridgeB6_1_6_2.selectedLeafB6_1_6_2Impossible

end Krenn.Component60.SelectedBridgeB6_1_6_2
