import KrennComponent48.Root
import KrennComponent48.SelectedLeafB5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component48.SelectedBridgeB5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component48.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 60 then
      d0Inverse0
    else d0Inverse2
  apply Krenn.Component48.SelectedLeafB5.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨135, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨165, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨178, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨196, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨200, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨202, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨204, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨209, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨216, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨228, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨239, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨240, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨348, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨354, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨358, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨382, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨399, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨404, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨433, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨465, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨472, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨473, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨483, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨569, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨576, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨577, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨620, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨626, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨628, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨632, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨634, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component48.Root.rootEquations, Krenn.Component48.SelectedLeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component48.SelectedBridgeB5.selectedLeafB5Impossible

end Krenn.Component48.SelectedBridgeB5
