import KrennComponent1.Root
import KrennComponent1.SelectedLeafB5_6_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component1.SelectedBridgeB5_6_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_6_7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 51 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 52 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 53 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 59 → R := fun index =>
    if inside : index.val < 57 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 57 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 61 → R := fun index =>
    if inside : index.val < 59 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 64 → R := fun index =>
    if inside : index.val < 61 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d2Inverse0
    else if at1 : index.val = 62 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component1.SelectedLeafB5_6_7.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨47, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨56, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨220, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨224, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨276, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨366, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨367, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨384, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨385, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨388, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨390, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨413, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨503, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨559, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨579, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB5_6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component1.SelectedBridgeB5_6_7.selectedLeafB5_6_7Impossible

end Krenn.Component1.SelectedBridgeB5_6_7
