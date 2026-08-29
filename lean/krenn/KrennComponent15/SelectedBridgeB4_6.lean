import KrennComponent15.Root
import KrennComponent15.SelectedLeafB4_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component15.SelectedBridgeB4_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component15.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 36 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 37 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 38 = 0)
    : False := by
  let values1 : Fin 58 → R := fun index =>
    if inside : index.val < 57 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 60 → R := fun index =>
    if inside : index.val < 58 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 58 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.Component15.SelectedLeafB4_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨178, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨209, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨226, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨227, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨234, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨315, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨364, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨365, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨366, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨367, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨368, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨379, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨423, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨481, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨496, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨506, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨519, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨546, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component15.Root.rootEquations, Krenn.Component15.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component15.SelectedBridgeB4_6.selectedLeafB4_6Impossible

end Krenn.Component15.SelectedBridgeB4_6
