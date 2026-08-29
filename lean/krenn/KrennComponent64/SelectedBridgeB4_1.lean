import KrennComponent64.Root
import KrennComponent64.SelectedLeafB4_1

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component64.SelectedBridgeB4_1

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component64.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 37 = 0)
    (d1Equation1 : values 38 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 39 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 61 → R := fun index =>
    if inside : index.val < 60 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.Component64.SelectedLeafB4_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨161, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨176, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨194, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨199, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨200, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨223, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨235, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨290, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨358, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨369, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨372, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨445, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨469, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨479, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨512, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨517, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨522, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨526, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨527, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨530, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨548, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨611, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨620, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨633, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨634, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component64.Root.rootEquations, Krenn.Component64.SelectedLeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component64.SelectedBridgeB4_1.selectedLeafB4_1Impossible

end Krenn.Component64.SelectedBridgeB4_1
