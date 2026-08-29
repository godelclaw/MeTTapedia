import KrennComponent20.Root
import KrennComponent20.SelectedLeafB4_4_6_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component20.SelectedBridgeB4_4_6_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_4_6_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component20.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 40 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 54 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 55 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 56 = 0)
    (d3Equation0 : values 25 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 27 * d3Inverse1 - 1 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 29 * d3Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  let values3 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d2Inverse0
    else d2Inverse1
  let values4 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d3Inverse1
    else d3Inverse2
  apply Krenn.Component20.SelectedLeafB4_4_6_3.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨405, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨530, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨579, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨634, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_4_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component20.SelectedBridgeB4_4_6_3.selectedLeafB4_4_6_3Impossible

end Krenn.Component20.SelectedBridgeB4_4_6_3
