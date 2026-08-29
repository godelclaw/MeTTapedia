import KrennComponent14.Root
import KrennComponent14.SelectedLeafB4_0_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component14.SelectedBridgeB4_0_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_0_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component14.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Equation1 : values 39 = 0)
    (d1Equation2 : values 40 = 0)
    (d2Equation0 : values 53 = 0)
    (d2Equation1 : values 54 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 55 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 60 → R := values1
  let values3 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values2 ⟨index.val, inside⟩
    else d2Inverse2
  apply Krenn.Component14.SelectedLeafB4_0_1.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨195, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨342, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB4_0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component14.SelectedBridgeB4_0_1.selectedLeafB4_0_1Impossible

end Krenn.Component14.SelectedBridgeB4_0_1
