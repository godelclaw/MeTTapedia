import KrennComponent10.Root
import KrennComponent10.SelectedLeafB6_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component10.SelectedBridgeB6_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Equation1 : values 40 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 41 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.Component10.SelectedLeafB6_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨165, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨189, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨409, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨473, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨550, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨595, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨634, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component10.SelectedBridgeB6_1.selectedLeafB6_1Impossible

end Krenn.Component10.SelectedBridgeB6_1
