import KrennComponent36.Root
import KrennComponent36.SelectedLeafB0_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component36.SelectedBridgeB0_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component36.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Equation1 : values 40 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  let values1 : Fin 62 → R := values
  let values2 : Fin 62 → R := values1
  apply Krenn.Component36.SelectedLeafB0_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨136, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨152, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨153, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨154, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨159, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨253, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨272, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨276, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨303, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨305, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨306, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨307, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨319, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨325, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨375, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨377, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨448, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨451, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨514, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨562, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨651, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨662, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component36.Root.rootEquations, Krenn.Component36.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component36.SelectedBridgeB0_0.selectedLeafB0_0Impossible

end Krenn.Component36.SelectedBridgeB0_0
