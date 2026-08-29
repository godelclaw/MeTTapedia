import KrennComponent60.Root
import KrennComponent60.SelectedLeafB0_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component60.SelectedBridgeB0_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 41 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 61 → R := values
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d1Inverse0
    else if at1 : index.val = 62 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.Component60.SelectedLeafB0_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨75, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨143, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨149, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨151, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨177, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨209, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨292, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨304, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨310, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨314, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨424, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨436, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨459, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨465, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨592, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨593, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨643, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component60.SelectedBridgeB0_7.selectedLeafB0_7Impossible

end Krenn.Component60.SelectedBridgeB0_7
