import KrennComponent6.Root
import KrennComponent6.SelectedLeafB4

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component6.SelectedBridgeB4

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component6.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  let values1 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  apply Krenn.Component6.SelectedLeafB4.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨147, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨185, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨195, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨201, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨204, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨205, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨206, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨209, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨212, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨213, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨214, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨238, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨240, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨255, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨259, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨261, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨264, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨275, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨310, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨334, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨368, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨369, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨370, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨371, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨372, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨373, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨374, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨375, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨385, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨386, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨387, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨391, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨392, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨394, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨409, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨410, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨417, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨418, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨424, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨428, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨429, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨490, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨496, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨512, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨513, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨518, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨538, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨539, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨540, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨541, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨542, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨571, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨572, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨596, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component6.SelectedBridgeB4.selectedLeafB4Impossible

end Krenn.Component6.SelectedBridgeB4
