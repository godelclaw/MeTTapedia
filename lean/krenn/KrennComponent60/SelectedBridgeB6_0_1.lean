import KrennComponent60.Root
import KrennComponent60.SelectedLeafB6_0_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component60.SelectedBridgeB6_0_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_0_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Equation1 : values 40 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Equation1 : values 56 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 63 → R := values1
  let values3 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component60.SelectedLeafB6_0_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨579, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component60.SelectedBridgeB6_0_1.selectedLeafB6_0_1Impossible

end Krenn.Component60.SelectedBridgeB6_0_1
