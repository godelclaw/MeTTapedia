import KrennComponent51.Root
import KrennComponent51.SelectedLeafB5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component51.SelectedBridgeB5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component51.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d0Inverse0
    else d0Inverse2
  apply Krenn.Component51.SelectedLeafB5.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨64, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨174, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨176, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨177, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨200, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨204, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨205, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨222, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨223, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨240, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨258, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨372, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨373, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨374, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨375, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨378, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨383, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨384, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨386, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨388, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨424, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨433, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨512, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component51.Root.rootEquations, Krenn.Component51.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component51.SelectedBridgeB5.selectedLeafB5Impossible

end Krenn.Component51.SelectedBridgeB5
