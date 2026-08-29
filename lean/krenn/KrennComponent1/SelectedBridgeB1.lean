import KrennComponent1.Root
import KrennComponent1.SelectedLeafB1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component1.SelectedBridgeB1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 58 → R := fun index =>
    if inside : index.val < 57 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  apply Krenn.Component1.SelectedLeafB1.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨258, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨264, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨265, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨266, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨267, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨274, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨276, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨354, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨373, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨384, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨385, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨391, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨408, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨489, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨505, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨523, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨546, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component1.SelectedBridgeB1.selectedLeafB1Impossible

end Krenn.Component1.SelectedBridgeB1
