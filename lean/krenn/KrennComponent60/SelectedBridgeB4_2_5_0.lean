import KrennComponent60.Root
import KrennComponent60.SelectedLeafB4_2_5_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component60.SelectedBridgeB4_2_5_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_2_5_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 55 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 56 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    (d3Equation0 : values 25 = 0)
    (d3Equation1 : values 28 = 0)
    (d3Equation2 : values 29 = 0)
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
      d2Inverse0
    else d2Inverse2
  let values4 : Fin 65 → R := values3
  apply Krenn.Component60.SelectedLeafB4_2_5_0.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨143, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨292, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨327, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨383, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨404, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨422, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨599, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_2_5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component60.SelectedBridgeB4_2_5_0.selectedLeafB4_2_5_0Impossible

end Krenn.Component60.SelectedBridgeB4_2_5_0
