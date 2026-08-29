import KrennComponent45.Root
import KrennComponent45.SelectedLeafB0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component45.SelectedBridgeB0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component45.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  let values1 : Fin 57 → R := values
  apply Krenn.Component45.SelectedLeafB0.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨243, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨252, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨253, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨254, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨255, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨267, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨379, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨380, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨386, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨388, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨514, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨559, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component45.Root.rootEquations, Krenn.Component45.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component45.SelectedBridgeB0.selectedLeafB0Impossible

end Krenn.Component45.SelectedBridgeB0
