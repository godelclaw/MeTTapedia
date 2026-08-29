import KrennComponent10.Root
import KrennComponent10.SelectedLeafB4_6

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component10.SelectedBridgeB4_6

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.Component10.SelectedLeafB4_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨174, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨176, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨177, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨180, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨181, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨185, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨186, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨197, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨277, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨284, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨286, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨311, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨322, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨343, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨356, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨358, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨368, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨369, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨409, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨432, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨446, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨473, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨492, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨512, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨513, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨527, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨542, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨547, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨550, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨568, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨579, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨599, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨611, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨613, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨633, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨634, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component10.Root.rootEquations, Krenn.Component10.SelectedLeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component10.SelectedBridgeB4_6.selectedLeafB4_6Impossible

end Krenn.Component10.SelectedBridgeB4_6
