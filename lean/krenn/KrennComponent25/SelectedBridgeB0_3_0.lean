import KrennComponent25.Root
import KrennComponent25.SelectedLeafB0_3_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component25.SelectedBridgeB0_3_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_3_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component25.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 41 * d1Inverse2 - 1 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Equation1 : values 56 = 0)
    (d2Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 61 → R := values
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d1Inverse1
    else d1Inverse2
  let values3 : Fin 63 → R := values2
  apply Krenn.Component25.SelectedLeafB0_3_0.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨177, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨238, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨239, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨306, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨310, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨313, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨388, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨406, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨435, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨439, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨469, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨588, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component25.Root.rootEquations, Krenn.Component25.SelectedLeafB0_3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component25.SelectedBridgeB0_3_0.selectedLeafB0_3_0Impossible

end Krenn.Component25.SelectedBridgeB0_3_0
