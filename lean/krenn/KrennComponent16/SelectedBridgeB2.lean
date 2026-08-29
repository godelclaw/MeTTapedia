import KrennComponent16.Root
import KrennComponent16.SelectedLeafB2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component16.SelectedBridgeB2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component16.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  apply Krenn.Component16.SelectedLeafB2.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨144, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨448, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨571, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component16.SelectedBridgeB2.selectedLeafB2Impossible

end Krenn.Component16.SelectedBridgeB2
