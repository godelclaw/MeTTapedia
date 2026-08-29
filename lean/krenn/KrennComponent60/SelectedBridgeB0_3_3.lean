import KrennComponent60.Root
import KrennComponent60.SelectedLeafB0_3_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component60.SelectedBridgeB0_3_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_3_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
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
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 61 → R := values
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component60.SelectedLeafB0_3_3.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨143, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨145, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨150, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨165, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨195, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨236, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨237, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨263, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨292, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨295, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨303, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨310, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨314, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨398, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨403, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨407, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨436, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨437, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨446, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨459, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨460, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨549, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨578, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨592, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨593, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨600, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨653, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component60.SelectedBridgeB0_3_3.selectedLeafB0_3_3Impossible

end Krenn.Component60.SelectedBridgeB0_3_3
