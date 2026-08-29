import KrennComponent56.Root
import KrennComponent56.SelectedLeafB6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component56.SelectedBridgeB6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component56.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  let values1 : Fin 59 → R := fun index =>
    if inside : index.val < 57 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 57 then
      d0Inverse0
    else d0Inverse1
  apply Krenn.Component56.SelectedLeafB6.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨208, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨209, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨212, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨214, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨226, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨234, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨235, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨236, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨237, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨241, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨242, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨243, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨263, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨274, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨365, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨366, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨372, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨373, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨383, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨398, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨416, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨417, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨472, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨473, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨527, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨546, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨547, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨549, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨575, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, Krenn.Component56.Root.rootEquations, Krenn.Component56.SelectedLeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component56.SelectedBridgeB6.selectedLeafB6Impossible

end Krenn.Component56.SelectedBridgeB6
