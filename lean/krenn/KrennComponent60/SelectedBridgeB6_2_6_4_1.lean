import KrennComponent60.Root
import KrennComponent60.SelectedLeafB6_2_6_4_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component60.SelectedBridgeB6_2_6_4_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_2_6_4_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 55 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 57 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 25 * d3Inverse0 - 1 = 0)
    (d3Equation1 : values 28 = 0)
    (d3Equation2 : values 29 = 0)
    (d4Equation0 : values 58 = 0)
    (d4Equation1 : values 59 = 0)
    (d4Inverse2 : R)
    (d4Equation2 : values 60 * d4Inverse2 - 1 = 0)
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
    else d1Inverse1
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d2Inverse0
    else d2Inverse1
  let values4 : Fin 67 → R := fun index =>
    if inside : index.val < 66 then
      values3 ⟨index.val, inside⟩
    else d3Inverse0
  let values5 : Fin 68 → R := fun index =>
    if inside : index.val < 67 then
      values4 ⟨index.val, inside⟩
    else d4Inverse2
  apply Krenn.Component60.SelectedLeafB6_2_6_4_1.selectedHasNoCommonZero values5
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_2_6_4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_2_6_4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_2_6_4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_2_6_4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_2_6_4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_2_6_4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_2_6_4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_2_6_4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_2_6_4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_2_6_4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_2_6_4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_2_6_4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d4Equation1

#print axioms Krenn.Component60.SelectedBridgeB6_2_6_4_1.selectedLeafB6_2_6_4_1Impossible

end Krenn.Component60.SelectedBridgeB6_2_6_4_1
