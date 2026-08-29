import KrennComponent20.Root
import KrennComponent20.SelectedLeafB4_6_0_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component20.SelectedBridgeB4_6_0_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_6_0_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component20.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Equation0 : values 54 = 0)
    (d2Equation1 : values 55 = 0)
    (d2Equation2 : values 56 = 0)
    (d3Equation0 : values 25 = 0)
    (d3Equation1 : values 27 = 0)
    (d3Equation2 : values 29 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 63 → R := values2
  let values4 : Fin 63 → R := values3
  apply Krenn.Component20.SelectedLeafB4_6_0_0.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨414, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨416, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨493, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨513, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨527, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨530, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨541, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨547, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨558, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨559, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨560, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨563, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨565, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨566, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨577, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨578, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨579, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨587, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨588, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨589, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨621, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨623, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨624, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨633, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨634, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component20.Root.rootEquations, Krenn.Component20.SelectedLeafB4_6_0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1

#print axioms Krenn.Component20.SelectedBridgeB4_6_0_0.selectedLeafB4_6_0_0Impossible

end Krenn.Component20.SelectedBridgeB4_6_0_0
