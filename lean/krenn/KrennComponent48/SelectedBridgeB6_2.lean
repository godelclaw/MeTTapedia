import KrennComponent48.Root
import KrennComponent48.SelectedLeafB6_2

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component48.SelectedBridgeB6_2

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component48.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.Component48.SelectedLeafB6_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨56, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨59, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨228, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨239, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨259, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨345, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨394, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨576, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨577, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨632, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨634, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component48.SelectedBridgeB6_2.selectedLeafB6_2Impossible

end Krenn.Component48.SelectedBridgeB6_2
