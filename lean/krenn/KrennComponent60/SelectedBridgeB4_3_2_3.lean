import KrennComponent60.Root
import KrennComponent60.SelectedLeafB4_3_2_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component60.SelectedBridgeB4_3_2_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_3_2_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 41 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 57 = 0)
    (d3Equation0 : values 25 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 28 * d3Inverse1 - 1 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 29 * d3Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  let values4 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d3Inverse1
    else d3Inverse2
  apply Krenn.Component60.SelectedLeafB4_3_2_3.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨165, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨264, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨293, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨310, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨404, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨436, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨592, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_3_2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0

#print axioms Krenn.Component60.SelectedBridgeB4_3_2_3.selectedLeafB4_3_2_3Impossible

end Krenn.Component60.SelectedBridgeB4_3_2_3
