import KrennComponent16.Root
import KrennComponent16.SelectedLeafB5_6_3_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component16.SelectedBridgeB5_6_3_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_6_3_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component16.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 41 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 42 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 43 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    (d3Equation0 : values 26 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 28 * d3Inverse1 - 1 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 31 * d3Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 68 → R := fun index =>
    if inside : index.val < 66 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 66 then
      d2Inverse1
    else d2Inverse2
  let values4 : Fin 70 → R := fun index =>
    if inside : index.val < 68 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 68 then
      d3Inverse1
    else d3Inverse2
  apply Krenn.Component16.SelectedLeafB5_6_3_3.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨150, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨151, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨153, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨273, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨317, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨506, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨512, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨532, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨593, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨660, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB5_6_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component16.SelectedBridgeB5_6_3_3.selectedLeafB5_6_3_3Impossible

end Krenn.Component16.SelectedBridgeB5_6_3_3
