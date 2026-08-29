import KrennComponent13.Root
import KrennComponent13.SelectedLeafB4_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component13.SelectedBridgeB4_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component13.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 37 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 38 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 39 = 0)
    : False := by
  let values1 : Fin 59 → R := fun index =>
    if inside : index.val < 58 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 61 → R := fun index =>
    if inside : index.val < 59 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 59 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.Component13.SelectedLeafB4_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨55, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨66, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨151, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨152, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨160, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨165, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨180, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨181, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨185, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨186, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨188, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨284, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨286, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨290, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨307, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨367, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨373, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨376, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨377, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨398, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨409, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨425, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨437, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨449, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨470, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨483, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨489, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨525, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨532, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨547, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨548, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨549, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨571, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component13.Root.rootEquations, Krenn.Component13.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component13.SelectedBridgeB4_6.selectedLeafB4_6Impossible

end Krenn.Component13.SelectedBridgeB4_6
