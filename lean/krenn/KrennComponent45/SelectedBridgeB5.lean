import KrennComponent45.Root
import KrennComponent45.SelectedLeafB5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component45.SelectedBridgeB5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component45.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 59 → R := fun index =>
    if inside : index.val < 57 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 57 then
      d0Inverse0
    else d0Inverse2
  apply Krenn.Component45.SelectedLeafB5.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨208, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨214, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨231, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨237, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨241, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨244, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨245, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨255, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨258, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨267, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨284, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨365, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨367, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨372, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨379, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨380, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨381, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨384, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨390, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨407, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨421, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨422, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨492, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨525, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨559, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component45.SelectedBridgeB5.selectedLeafB5Impossible

end Krenn.Component45.SelectedBridgeB5
