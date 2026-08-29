import KrennComponent16.Root
import KrennComponent16.SelectedLeafB1_4

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component16.SelectedBridgeB1_4

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB1_4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component16.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 41 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 42 = 0)
    (d1Equation2 : values 43 = 0)
    : False := by
  let values1 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 63 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.Component16.SelectedLeafB1_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨53, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨147, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨175, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨314, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨343, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨407, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨433, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨448, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨455, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨468, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨481, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨501, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨527, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨571, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨649, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨660, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨661, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component16.Root.rootEquations, Krenn.Component16.SelectedLeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component16.SelectedBridgeB1_4.selectedLeafB1_4Impossible

end Krenn.Component16.SelectedBridgeB1_4
