import KrennComponent54.Root
import KrennComponent54.SelectedLeafB0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component54.SelectedBridgeB0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component54.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  let values1 : Fin 61 → R := values
  apply Krenn.Component54.SelectedLeafB0.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨165, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨223, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨288, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨351, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨364, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨398, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨439, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨474, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨531, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨545, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨561, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨624, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨636, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨638, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component54.Root.rootEquations, Krenn.Component54.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component54.SelectedBridgeB0.selectedLeafB0Impossible

end Krenn.Component54.SelectedBridgeB0
