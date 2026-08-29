import KrennComponent39.Root
import KrennComponent39.SelectedLeafB1_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component39.SelectedBridgeB1_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB1_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component39.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Equation1 : values 39 = 0)
    (d1Equation2 : values 40 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 62 → R := values1
  apply Krenn.Component39.SelectedLeafB1_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨181, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨187, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨192, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨195, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨232, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨234, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨237, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨250, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨254, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨277, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨282, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨303, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨304, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨305, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨322, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨324, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨342, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨354, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨365, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨369, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨380, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨396, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨397, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨399, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨410, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨416, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨419, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨422, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨427, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨430, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨441, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨444, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨460, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨505, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨532, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨562, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨568, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨570, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨571, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨614, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨644, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨649, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨659, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨660, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component39.SelectedBridgeB1_0.selectedLeafB1_0Impossible

end Krenn.Component39.SelectedBridgeB1_0
