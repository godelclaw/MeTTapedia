import KrennComponent14.Root
import KrennComponent14.SelectedLeafB0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component14.SelectedBridgeB0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component14.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  let values1 : Fin 59 → R := values
  apply Krenn.Component14.SelectedLeafB0.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨132, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨136, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨138, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨195, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨344, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨351, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨365, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨460, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨465, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨524, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨633, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component14.Root.rootEquations, Krenn.Component14.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component14.SelectedBridgeB0.selectedLeafB0Impossible

end Krenn.Component14.SelectedBridgeB0
