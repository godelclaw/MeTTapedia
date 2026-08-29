import KrennComponent48.Root
import KrennComponent48.SelectedLeafB6_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component48.SelectedBridgeB6_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component48.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 62 → R := values1
  apply Krenn.Component48.SelectedLeafB6_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨197, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨228, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨239, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨241, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨319, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨404, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨435, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨472, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨484, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨634, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component48.SelectedBridgeB6_0.selectedLeafB6_0Impossible

end Krenn.Component48.SelectedBridgeB6_0
