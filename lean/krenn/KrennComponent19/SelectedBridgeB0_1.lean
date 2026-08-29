import KrennComponent19.Root
import KrennComponent19.SelectedLeafB0_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component19.SelectedBridgeB0_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component19.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 42 = 0)
    (d1Equation1 : values 43 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 44 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := values
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.Component19.SelectedLeafB0_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨200, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨304, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨420, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨424, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨429, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨565, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨610, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨662, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component19.SelectedBridgeB0_1.selectedLeafB0_1Impossible

end Krenn.Component19.SelectedBridgeB0_1
