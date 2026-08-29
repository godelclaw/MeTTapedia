import KrennComponent10.Root
import KrennComponent10.SelectedLeafB5_6_2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component10.SelectedBridgeB5_6_2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_6_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Equation0 : values 54 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 55 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 56 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else d2Inverse1
  apply Krenn.Component10.SelectedLeafB5_6_2.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨69, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨446, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨465, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨473, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨490, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨499, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨550, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨595, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨634, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB5_6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component10.SelectedBridgeB5_6_2.selectedLeafB5_6_2Impossible

end Krenn.Component10.SelectedBridgeB5_6_2
