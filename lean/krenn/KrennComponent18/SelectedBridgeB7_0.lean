import KrennComponent18.Root
import KrennComponent18.SelectedLeafB7_0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component18.SelectedBridgeB7_0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB7_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component18.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 41 = 0)
    (d1Equation1 : values 42 = 0)
    (d1Equation2 : values 43 = 0)
    : False := by
  let values1 : Fin 64 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      d0Inverse0
    else if at1 : index.val = 62 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 64 → R := values1
  apply Krenn.Component18.SelectedLeafB7_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨113, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨143, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨145, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨147, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨148, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨159, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨246, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨271, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨295, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨315, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨327, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨408, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨409, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨430, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨433, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨435, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨437, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨442, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨449, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨479, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨506, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨511, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨557, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨562, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨606, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨645, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨649, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨656, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component18.Root.rootEquations, Krenn.Component18.SelectedLeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component18.SelectedBridgeB7_0.selectedLeafB7_0Impossible

end Krenn.Component18.SelectedBridgeB7_0
