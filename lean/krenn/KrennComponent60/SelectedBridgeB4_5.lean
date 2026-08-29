import KrennComponent60.Root
import KrennComponent60.SelectedLeafB4_5

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component60.SelectedBridgeB4_5

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 40 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 41 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.Component60.SelectedLeafB4_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨143, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨145, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨151, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨154, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨159, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨177, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨198, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨223, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨231, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨302, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨306, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨308, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨314, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨331, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨365, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨377, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨423, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨424, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨431, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨436, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨443, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨500, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨522, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨523, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨525, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨539, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨556, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨578, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨593, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨604, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨605, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨654, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, Krenn.Component60.Root.rootEquations, Krenn.Component60.SelectedLeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2

#print axioms Krenn.Component60.SelectedBridgeB4_5.selectedLeafB4_5Impossible

end Krenn.Component60.SelectedBridgeB4_5
