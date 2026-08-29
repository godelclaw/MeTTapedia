import KrennComponent60.Root
import KrennComponent60.SelectedLeafB6_1_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component60.SelectedBridgeB6_1_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_1_1Impossible {R : Type*} [Field R] [CharZero R]
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
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component60.SelectedLeafB6_1_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨154, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨155, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨177, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨178, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨223, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨236, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨264, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨292, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨308, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨310, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨365, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨377, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨378, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨383, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨404, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨431, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨500, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨525, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨537, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨539, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨579, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨605, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨621, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨654, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB6_1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component60.SelectedBridgeB6_1_1.selectedLeafB6_1_1Impossible

end Krenn.Component60.SelectedBridgeB6_1_1
