import KrennComponent58.Root
import KrennComponent58.SelectedLeafB0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component58.SelectedBridgeB0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component58.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  let values1 : Fin 59 → R := values
  apply Krenn.Component58.SelectedLeafB0.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨225, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨227, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨228, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨315, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨340, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨342, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨459, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨474, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨482, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨561, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component58.Root.rootEquations, Krenn.Component58.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component58.SelectedBridgeB0.selectedLeafB0Impossible

end Krenn.Component58.SelectedBridgeB0
