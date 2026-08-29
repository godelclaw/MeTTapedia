import KrennComponent19.Root
import KrennComponent19.SelectedLeafB5_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component19.SelectedBridgeB5_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component19.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 42 = 0)
    (d1Equation1 : values 43 = 0)
    (d1Equation2 : values 44 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 64 → R := values1
  apply Krenn.Component19.SelectedLeafB5_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨216, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨220, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨291, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨304, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨319, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨418, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨420, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨422, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨424, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨429, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨439, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨442, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨470, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨565, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨605, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨646, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨654, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨662, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component19.Root.rootEquations, Krenn.Component19.SelectedLeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component19.SelectedBridgeB5_0.selectedLeafB5_0Impossible

end Krenn.Component19.SelectedBridgeB5_0
