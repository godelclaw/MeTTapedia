import KrennComponent12.Root
import KrennComponent12.SelectedLeafB4_6_7_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component12.SelectedBridgeB4_6_7_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_6_7_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component12.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 38 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 39 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 40 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 53 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 54 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 55 * d2Inverse2 - 1 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 23 * d3Inverse0 - 1 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 25 * d3Inverse1 - 1 = 0)
    (d3Equation2 : values 28 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 62 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d2Inverse0
    else if at1 : index.val = 63 then
      d2Inverse1
    else d2Inverse2
  let values4 : Fin 67 → R := fun index =>
    if inside : index.val < 65 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d3Inverse0
    else d3Inverse1
  apply Krenn.Component12.SelectedLeafB4_6_7_6.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_6_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_6_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_6_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_6_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨214, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_6_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨338, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_6_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨339, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_6_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_6_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨400, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_6_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨407, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_6_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨492, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_6_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨549, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_6_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_6_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_6_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_6_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component12.Root.rootEquations, Krenn.Component12.SelectedLeafB4_6_7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component12.SelectedBridgeB4_6_7_6.selectedLeafB4_6_7_6Impossible

end Krenn.Component12.SelectedBridgeB4_6_7_6
