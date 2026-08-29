import KrennComponent25.Root
import KrennComponent25.SelectedLeafB6_6_6_6_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component25.SelectedBridgeB6_6_6_6_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_6_6_6_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component25.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 55 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 57 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 24 * d3Inverse0 - 1 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 26 * d3Inverse1 - 1 = 0)
    (d3Equation2 : values 29 = 0)
    (d4Equation0 : values 58 = 0)
    (d4Equation1 : values 59 = 0)
    (d4Equation2 : values 60 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d2Inverse0
    else d2Inverse1
  let values4 : Fin 69 → R := fun index =>
    if inside : index.val < 67 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 67 then
      d3Inverse0
    else d3Inverse1
  let values5 : Fin 69 → R := values4
  apply Krenn.Component25.SelectedLeafB6_6_6_6_0.selectedHasNoCommonZero values5
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB6_6_6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB6_6_6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB6_6_6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨148, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB6_6_6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB6_6_6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨435, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB6_6_6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB6_6_6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB6_6_6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB6_6_6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB6_6_6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB6_6_6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB6_6_6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, values5, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB6_6_6_6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d4Equation2

#print axioms Krenn.Component25.SelectedBridgeB6_6_6_6_0.selectedLeafB6_6_6_6_0Impossible

end Krenn.Component25.SelectedBridgeB6_6_6_6_0
