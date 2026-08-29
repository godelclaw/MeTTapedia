import KrennComponent39.Root
import KrennComponent39.SelectedLeafB4_2_3_7

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component39.SelectedBridgeB4_2_3_7

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB4_2_3_7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component39.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 39 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 40 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 23 * d3Inverse0 - 1 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 25 * d3Inverse1 - 1 = 0)
    (d3Inverse2 : R)
    (d3Equation2 : values 28 * d3Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  let values3 : Fin 65 → R := fun index =>
    if inside : index.val < 63 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 63 then
      d2Inverse1
    else d2Inverse2
  let values4 : Fin 68 → R := fun index =>
    if inside : index.val < 65 then
      values3 ⟨index.val, inside⟩
    else if at0 : index.val = 65 then
      d3Inverse0
    else if at1 : index.val = 66 then
      d3Inverse1
    else d3Inverse2
  apply Krenn.Component39.SelectedLeafB4_2_3_7.selectedHasNoCommonZero values4
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨62, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨63, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨68, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨69, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨129, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨176, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨190, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨232, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨277, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨280, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨300, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨304, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨305, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨306, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨307, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨308, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨318, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨349, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨353, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨355, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨390, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨426, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨430, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨441, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨451, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨452, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨456, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨461, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨462, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨472, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨502, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨511, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨512, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨513, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨516, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨519, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨532, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨570, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨574, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨580, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨600, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨607, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨625, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨658, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨659, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨660, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation1
  · simpa [sub_eq_add_neg, values1, values2, values3, values4, Krenn.Component39.Root.rootEquations, Krenn.Component39.SelectedLeafB4_2_3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d3Equation2

#print axioms Krenn.Component39.SelectedBridgeB4_2_3_7.selectedLeafB4_2_3_7Impossible

end Krenn.Component39.SelectedBridgeB4_2_3_7
