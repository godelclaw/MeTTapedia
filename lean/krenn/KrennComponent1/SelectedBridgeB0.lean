import KrennComponent1.Root
import KrennComponent1.SelectedLeafB0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component1.SelectedBridgeB0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  let values1 : Fin 57 → R := values
  apply Krenn.Component1.SelectedLeafB0.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨264, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨265, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨266, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨267, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨276, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨354, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨384, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨385, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨391, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component1.SelectedBridgeB0.selectedLeafB0Impossible

end Krenn.Component1.SelectedBridgeB0
