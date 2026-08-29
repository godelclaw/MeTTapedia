import KrennComponent1.Root
import KrennComponent1.SelectedLeafB6_2_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component1.SelectedBridgeB6_2_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6_2_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 51 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 52 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 53 = 0)
    : False := by
  let values1 : Fin 59 → R := fun index =>
    if inside : index.val < 57 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 57 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 60 → R := fun index =>
    if inside : index.val < 59 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d2Inverse0
    else d2Inverse1
  apply Krenn.Component1.SelectedLeafB6_2_6.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB6_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB6_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB6_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB6_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB6_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨276, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB6_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨366, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB6_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨384, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB6_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨385, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB6_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB6_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB6_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB6_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB6_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB6_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component1.Root.rootEquations, Krenn.Component1.SelectedLeafB6_2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component1.SelectedBridgeB6_2_6.selectedLeafB6_2_6Impossible

end Krenn.Component1.SelectedBridgeB6_2_6
