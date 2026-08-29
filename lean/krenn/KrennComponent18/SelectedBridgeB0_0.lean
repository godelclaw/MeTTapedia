import KrennComponent18.Root
import KrennComponent18.SelectedLeafB0_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component18.SelectedBridgeB0_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component18.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 41 = 0)
    (d1Equation1 : values 42 = 0)
    (d1Equation2 : values 43 = 0)
    : False := by
  let values1 : Fin 61 → R := values
  let values2 : Fin 61 → R := values1
  apply Krenn.Component18.SelectedLeafB0_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨142, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨145, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨148, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨149, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨153, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨156, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨159, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨279, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨308, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨317, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨319, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨387, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨437, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨506, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨518, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨550, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨551, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨561, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨562, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨591, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨645, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨656, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component18.SelectedBridgeB0_0.selectedLeafB0_0Impossible

end Krenn.Component18.SelectedBridgeB0_0
