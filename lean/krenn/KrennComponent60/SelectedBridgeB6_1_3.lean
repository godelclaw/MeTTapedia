import KrennComponent60.Root
import KrennComponent60.SelectedLeafB6_1_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component60.SelectedBridgeB6_1_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_1_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Equation1 : values 40 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 41 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component60.SelectedLeafB6_1_3.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨143, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨150, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨165, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨178, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨240, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨264, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨273, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨292, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨293, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨298, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨303, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨305, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨308, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨310, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨314, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨383, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨389, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨398, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨404, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨422, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨423, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨427, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨433, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨435, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨436, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨437, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨442, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨454, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨470, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨548, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨578, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨579, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨587, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨593, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨600, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨653, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component60.SelectedBridgeB6_1_3.selectedLeafB6_1_3Impossible

end Krenn.Component60.SelectedBridgeB6_1_3
